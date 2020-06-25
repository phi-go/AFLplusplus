/*
   american fuzzy lop++ - LLVM instrumentation bootstrap
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski

   LLVM integration design comes from Laszlo Szekeres.

   Copyright 2015, 2016 Google Inc. All rights reserved.
   Copyright 2019-2020 AFLplusplus Project. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This code is the rewrite of afl-as.h's main_payload.

*/
#define _GNU_SOURCE

#ifdef __ANDROID__
#include "android-ashmem.h"
#endif
#include "config.h"
#include "types.h"
#include "cmplog.h"
#include "llvm-ngram-coverage.h"

#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>
#include <string.h>
#include <assert.h>
#include <stdint.h>
#include <errno.h>


#include <sys/time.h>
#include <time.h>

#include <sys/mman.h>
#include <sys/shm.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <sys/mman.h>

#include <ucontext.h>

#include <uthash.h>
#include <utlist.h>

#include <execinfo.h>

#ifdef __linux__
#include "snapshot-inl.h"
#endif

/* This is a somewhat ugly hack for the experimental 'trace-pc-guard' mode.
   Basically, we need to make sure that the forkserver is initialized after
   the LLVM-generated runtime initialization pass, not before. */

#define CONST_PRIO 5

#ifndef MAP_FIXED_NOREPLACE
#define MAP_FIXED_NOREPLACE MAP_FIXED
#endif

#include <sys/mman.h>
#include <fcntl.h>

/* Globals needed by the injected instrumentation. The __afl_area_initial region
   is used for instrumentation output before __afl_map_shm() has a chance to
   run. It will end up as .comm, so it shouldn't be too wasteful. */

u8  __afl_area_initial[MAP_SIZE];
u8 *__afl_area_ptr = __afl_area_initial;
u8 *__afl_dictionary;

u32 __afl_final_loc;
u32 __afl_map_size = MAP_SIZE;
u32 __afl_dictionary_len;
u64 __afl_map_addr;

#ifdef __ANDROID__
PREV_LOC_T __afl_prev_loc[NGRAM_SIZE_MAX];
u32        __afl_prev_ctx;
u32        __afl_cmp_counter;
#else
__thread PREV_LOC_T __afl_prev_loc[NGRAM_SIZE_MAX];
__thread u32        __afl_prev_ctx;
__thread u32        __afl_cmp_counter;
#endif

struct cmp_map *__afl_cmp_map;

/* Running in persistent mode? */

static u8 is_persistent;

/* Error reporting to forkserver controller */

void send_forkserver_error(int error) {

  u32 status;
  if (!error || error > 0xffff) return;
  status = (FS_OPT_ERROR | FS_OPT_SET_ERROR(error));
  if (write(FORKSRV_FD + 1, (char *)&status, 4) != 4) return;

}

/* SHM setup. */

static void __afl_map_shm(void) {

  char *id_str = getenv(SHM_ENV_VAR);

  if (__afl_final_loc) {

    __afl_map_size = __afl_final_loc;
    if (__afl_final_loc > MAP_SIZE) {

      char *ptr;
      u32   val = 0;
      if ((ptr = getenv("AFL_MAP_SIZE")) != NULL) val = atoi(ptr);
      if (val < __afl_final_loc) {

        if (__afl_final_loc > FS_OPT_MAX_MAPSIZE) {

          fprintf(stderr,
                  "Error: AFL++ tools *require* to set AFL_MAP_SIZE to %u to "
                  "be able to run this instrumented program!\n",
                  __afl_final_loc);
          if (id_str) {

            send_forkserver_error(FS_ERROR_MAP_SIZE);
            exit(-1);

          }

        } else {

          fprintf(stderr,
                  "Warning: AFL++ tools will need to set AFL_MAP_SIZE to %u to "
                  "be able to run this instrumented program!\n",
                  __afl_final_loc);

        }

      }

    }

  }

  /* If we're running under AFL, attach to the appropriate region, replacing the
     early-stage __afl_area_initial region that is needed to allow some really
     hacky .init code to work correctly in projects such as OpenSSL. */

  if (getenv("AFL_DEBUG"))
    fprintf(stderr,
            "DEBUG: id_str %s, __afl_map_addr 0x%llx, MAP_SIZE %u, "
            "__afl_final_loc %u, max_size_forkserver %u/0x%x\n",
            id_str == NULL ? "<null>" : id_str, __afl_map_addr, MAP_SIZE,
            __afl_final_loc, FS_OPT_MAX_MAPSIZE, FS_OPT_MAX_MAPSIZE);

  if (id_str) {

#ifdef USEMMAP
    const char *   shm_file_path = id_str;
    int            shm_fd = -1;
    unsigned char *shm_base = NULL;

    /* create the shared memory segment as if it was a file */
    shm_fd = shm_open(shm_file_path, O_RDWR, 0600);
    if (shm_fd == -1) {

      fprintf(stderr, "shm_open() failed\n");
      send_forkserver_error(FS_ERROR_SHM_OPEN);
      exit(1);

    }

    /* map the shared memory segment to the address space of the process */
    if (__afl_map_addr) {

      shm_base =
          mmap((void *)__afl_map_addr, __afl_map_size, PROT_READ | PROT_WRITE,
               MAP_FIXED_NOREPLACE | MAP_SHARED, shm_fd, 0);

    } else {

      shm_base = mmap(0, __afl_map_size, PROT_READ | PROT_WRITE, MAP_SHARED,
                      shm_fd, 0);

    }

    if (shm_base == MAP_FAILED) {

      close(shm_fd);
      shm_fd = -1;

      fprintf(stderr, "mmap() failed\n");
      if (__afl_map_addr)
        send_forkserver_error(FS_ERROR_MAP_ADDR);
      else
        send_forkserver_error(FS_ERROR_MMAP);
      exit(2);

    }

    __afl_area_ptr = shm_base;
#else
    u32 shm_id = atoi(id_str);

    __afl_area_ptr = shmat(shm_id, (void *)__afl_map_addr, 0);

#endif

    /* Whooooops. */

    if (__afl_area_ptr == (void *)-1) {

      if (__afl_map_addr)
        send_forkserver_error(FS_ERROR_MAP_ADDR);
      else
        send_forkserver_error(FS_ERROR_SHMAT);
      _exit(1);

    }

    /* Write something into the bitmap so that even with low AFL_INST_RATIO,
       our parent doesn't give up on us. */

    __afl_area_ptr[0] = 1;

  } else if (__afl_map_addr) {

    __afl_area_ptr =
        mmap((void *)__afl_map_addr, __afl_map_size, PROT_READ | PROT_WRITE,
             MAP_FIXED_NOREPLACE | MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (__afl_area_ptr == MAP_FAILED) {

      fprintf(stderr, "can not aquire mmap for address %p\n",
              (void *)__afl_map_addr);
      exit(1);

    }

  }

  id_str = getenv(CMPLOG_SHM_ENV_VAR);

  if (id_str) {

#ifdef USEMMAP
    const char *   shm_file_path = id_str;
    int            shm_fd = -1;
    unsigned char *shm_base = NULL;

    /* create the shared memory segment as if it was a file */
    shm_fd = shm_open(shm_file_path, O_RDWR, 0600);
    if (shm_fd == -1) {

      fprintf(stderr, "shm_open() failed\n");
      exit(1);

    }

    /* map the shared memory segment to the address space of the process */
    shm_base = mmap(0, sizeof(struct cmp_map), PROT_READ | PROT_WRITE,
                    MAP_SHARED, shm_fd, 0);
    if (shm_base == MAP_FAILED) {

      close(shm_fd);
      shm_fd = -1;

      fprintf(stderr, "mmap() failed\n");
      exit(2);

    }

    __afl_cmp_map = shm_base;
#else
    u32 shm_id = atoi(id_str);

    __afl_cmp_map = shmat(shm_id, NULL, 0);
#endif

    if (__afl_cmp_map == (void *)-1) _exit(1);

  }

}

#ifdef __linux__
static void __afl_start_snapshots(void) {

  static u8 tmp[4] = {0, 0, 0, 0};
  s32       child_pid;
  u32       status = 0;
  u32       already_read_first = 0;
  u32       was_killed;

  u8 child_stopped = 0;

  void (*old_sigchld_handler)(int) = 0;  // = signal(SIGCHLD, SIG_DFL);

  /* Phone home and tell the parent that we're OK. If parent isn't there,
     assume we're not running in forkserver mode and just execute program. */

  status |= (FS_OPT_ENABLED | FS_OPT_SNAPSHOT);
  if (__afl_map_size <= FS_OPT_MAX_MAPSIZE)
    status |= (FS_OPT_SET_MAPSIZE(__afl_map_size) | FS_OPT_MAPSIZE);
  if (__afl_dictionary_len > 0 && __afl_dictionary) status |= FS_OPT_AUTODICT;
  memcpy(tmp, &status, 4);

  if (write(FORKSRV_FD + 1, tmp, 4) != 4) return;

  if (__afl_dictionary_len > 0 && __afl_dictionary) {

    if (read(FORKSRV_FD, &was_killed, 4) != 4) _exit(1);

    if ((was_killed & (FS_OPT_ENABLED | FS_OPT_AUTODICT)) ==
        (FS_OPT_ENABLED | FS_OPT_AUTODICT)) {

      // great lets pass the dictionary through the forkserver FD
      u32 len = __afl_dictionary_len, offset = 0;
      s32 ret;

      if (write(FORKSRV_FD + 1, &len, 4) != 4) {

        write(2, "Error: could not send dictionary len\n",
              strlen("Error: could not send dictionary len\n"));
        _exit(1);

      }

      while (len != 0) {

        ret = write(FORKSRV_FD + 1, __afl_dictionary + offset, len);

        if (ret < 1) {

          write(2, "Error: could not send dictionary\n",
                strlen("Error: could not send dictionary\n"));
          _exit(1);

        }

        len -= ret;
        offset += ret;

      }

    } else {

      // uh this forkserver master does not understand extended option passing
      // or does not want the dictionary
      already_read_first = 1;

    }

  }

  while (1) {

    int status;

    if (already_read_first) {

      already_read_first = 0;

    } else {

      /* Wait for parent by reading from the pipe. Abort if read fails. */
      if (read(FORKSRV_FD, &was_killed, 4) != 4) _exit(1);

    }

    /* If we stopped the child in persistent mode, but there was a race
       condition and afl-fuzz already issued SIGKILL, write off the old
       process. */

    if (child_stopped && was_killed) {

      child_stopped = 0;
      if (waitpid(child_pid, &status, 0) < 0) _exit(1);

    }

    if (!child_stopped) {

      /* Once woken up, create a clone of our process. */

      child_pid = fork();
      if (child_pid < 0) _exit(1);

      /* In child process: close fds, resume execution. */

      if (!child_pid) {

        signal(SIGCHLD, old_sigchld_handler);

        close(FORKSRV_FD);
        close(FORKSRV_FD + 1);

        if (!afl_snapshot_do()) { raise(SIGSTOP); }

        __afl_area_ptr[0] = 1;
        memset(__afl_prev_loc, 0, NGRAM_SIZE_MAX * sizeof(PREV_LOC_T));

        return;

      }

    } else {

      /* Special handling for persistent mode: if the child is alive but
         currently stopped, simply restart it with SIGCONT. */

      kill(child_pid, SIGCONT);
      child_stopped = 0;

    }

    /* In parent process: write PID to pipe, then wait for child. */

    if (write(FORKSRV_FD + 1, &child_pid, 4) != 4) _exit(1);

    if (waitpid(child_pid, &status, WUNTRACED) < 0) _exit(1);

    /* In persistent mode, the child stops itself with SIGSTOP to indicate
       a successful run. In this case, we want to wake it up without forking
       again. */

    if (WIFSTOPPED(status)) child_stopped = 1;

    /* Relay wait status to pipe, then loop back. */

    if (write(FORKSRV_FD + 1, &status, 4) != 4) _exit(1);

  }

}

#endif

FILE * put_err_log_fp = NULL;

#define FPRINTF_TO_ERR_FILE(...) \
  do { \
    if (put_err_log_fp != NULL) { \
      fprintf(put_err_log_fp, __VA_ARGS__); \
      fflush(put_err_log_fp); \
    } else { \
      fprintf(stderr, __VA_ARGS__); \
      fflush(stderr); \
    } \
  } while(0)

#define READ_FROM_COMMAND_PIPE__BASE(ERR, V, S) \
  { \
    int res; \
    while ((res = read(FORKSRV_FD + 2, V, S)) == 0) { \
      ; \
    } \
    if (res != S) { \
      FPRINTF_TO_ERR_FILE("command read failed: %d %s %s:%d\n", \
                          res, strerror(errno), __FILE__, __LINE__); \
      ERR = 1; \
    } \
  }

#define READ_FROM_COMMAND_PIPE2(V, S) \
  do { \
    int err = 0; \
    READ_FROM_COMMAND_PIPE__BASE(err, V, S); \
    if (err) { \
      raise(SIGSTOP); \
      abort(); \
    } \
  } while(0)

#define READ_FROM_COMMAND_PIPE(V) \
  do { \
    int err = 0; \
    READ_FROM_COMMAND_PIPE__BASE(err, &V, sizeof(V)); \
    if (err) { \
      raise(SIGSTOP); \
      abort(); \
    } \
  } while(0)

#define WRITE_TO_COMMAND_PIPE(V, S) \
  { \
    int res; \
    if (((res = write(FORKSRV_FD + 3, V, S)) != S)) { \
      FPRINTF_TO_ERR_FILE("command write failed %d %s %s:%d\n", \
                          res, strerror(errno), __FILE__, __LINE__); \
      raise(SIGSTOP); \
      abort(); \
    } \
  }

#define NULL_CHECK(P) \
  if (P == NULL) { \
      FPRINTF_TO_ERR_FILE("ptr should not be null %s:%d\n", __FILE__, __LINE__); \
      raise(SIGSTOP); \
      _exit(1); \
  }

struct BBReq {
  void * pos;
  int size;
};

// https://en.wikipedia.org/wiki/X_Macro
// this allows the byte code to be generated as enum and as a string by the preprocessor
#define ANN_BYTE_CODE(X) \
  \
  X(START_VAL) \
  X(VAL_IMM) X(VAL_REG) X(VAL_MEM) X(VAL_PTR) X(DISP_NEG) X(DISP_POS) \
  X(END_VAL) \
  \
  X(START_REG) \
  X(NO_REG) \
  X(AH) X(AL) X(AX) X(BH) X(BL) X(BP) X(BPL) X(BX) X(CH) X(CL) X(CS) X(CX) X(DH) X(DI) X(DIL) \
  X(DL) X(DS) X(DX) X(EAX) X(EBP) X(EBX) X(ECX) X(EDI) X(EDX) X(EFLAGS) \
  X(EIP) X(EIZ) X(ES) X(ESI) X(ESP) X(FPSW) X(FS) X(GS) X(IP) X(RAX) X(RBP) X(RBX) X(RCX) X(RDI) \
  X(RDX) X(RIP) X(RIZ) X(RSI) X(RSP) X(SI) X(SIL) X(SP) X(SPL) X(SS) \
  X(CR0) X(CR1) X(CR2) X(CR3) X(CR4) X(CR5) X(CR6) X(CR7) X(CR8) X(CR9) X(CR10) X(CR11) X(CR12) \
  X(CR13) X(CR14) X(CR15) \
  X(DR0) X(DR1) X(DR2) X(DR3) X(DR4) X(DR5) X(DR6) X(DR7) X(DR8) X(DR9) X(DR10) X(DR11) X(DR12) \
  X(DR13) X(DR14) X(DR15) \
  X(FP0) X(FP1) X(FP2) X(FP3) X(FP4) X(FP5) X(FP6) X(FP7) \
  X(K0) X(K1) X(K2) X(K3) X(K4) X(K5) X(K6) X(K7) \
  X(MM0) X(MM1) X(MM2) X(MM3) X(MM4) X(MM5) X(MM6) X(MM7) \
  X(R8) X(R9) X(R10) X(R11) X(R12) X(R13) X(R14) X(R15) \
  X(ST0) X(ST1) X(ST2) X(ST3) X(ST4) X(ST5) X(ST6) X(ST7) \
  X(XMM0) X(XMM1) X(XMM2) X(XMM3) X(XMM4) X(XMM5) X(XMM6) X(XMM7) X(XMM8) X(XMM9) X(XMM10) X(XMM11) \
  X(XMM12) X(XMM13) X(XMM14) X(XMM15) X(XMM16) \
  X(XMM17) X(XMM18) X(XMM19) X(XMM20) X(XMM21) X(XMM22) X(XMM23) X(XMM24) X(XMM25) X(XMM26) X(XMM27) \
  X(XMM28) X(XMM29) X(XMM30) X(XMM31) \
  X(YMM0) X(YMM1) X(YMM2) X(YMM3) X(YMM4) X(YMM5) X(YMM6) X(YMM7) X(YMM8) X(YMM9) X(YMM10) X(YMM11) \
  X(YMM12) X(YMM13) X(YMM14) X(YMM15) X(YMM16) \
  X(YMM17) X(YMM18) X(YMM19) X(YMM20) X(YMM21) X(YMM22) X(YMM23) X(YMM24) X(YMM25) X(YMM26) X(YMM27) \
  X(YMM28) X(YMM29) X(YMM30) X(YMM31) \
  X(ZMM0) X(ZMM1) X(ZMM2) X(ZMM3) X(ZMM4) X(ZMM5) X(ZMM6) X(ZMM7) X(ZMM8) X(ZMM9) X(ZMM10) X(ZMM11) \
  X(ZMM12) X(ZMM13) X(ZMM14) X(ZMM15) X(ZMM16) \
  X(ZMM17) X(ZMM18) X(ZMM19) X(ZMM20) X(ZMM21) X(ZMM22) X(ZMM23) X(ZMM24) X(ZMM25) X(ZMM26) X(ZMM27) \
  X(ZMM28) X(ZMM29) X(ZMM30) X(ZMM31) \
  X(R8B) X(R9B) X(R10B) X(R11B) X(R12B) X(R13B) X(R14B) X(R15B) X(R8D) X(R9D) X(R10D) X(R11D) X(R12D) \
  X(R13D) X(R14D) X(R15D) X(R8W) X(R9W) X(R10W) X(R11W) X(R12W) X(R13W) X(R14W) X(R15W) \
  X(END_REG) \
  \
  X(START_FUNC) \
  X(CALC_ABS) X(CALC_SUB) X(CALC_HAMMING) X(CALC_HAMMING_FOR) \
  X(END_FUNC) \
  \
  X(START_GOAL) \
  X(GOAL_MIN) X(GOAL_SET) X(GOAL_MAX) X(GOAL_EDGE_COV) X(GOAL_EDGE_MEM_COV) \
  X(END_GOAL) \
  \
  X(MAX_BYTE_CODE)

#define X_AS_ENUM(ENUM) ENUM,
#define X_AS_STRING(STRING) #STRING,

typedef enum {
  ANN_BYTE_CODE(X_AS_ENUM)
} annotation_byte_code_t;

static const char *annotation_byte_code_strings[] = {
  ANN_BYTE_CODE(X_AS_STRING)
};

static const char * bc_str(annotation_byte_code_t bc) {
  return annotation_byte_code_strings[bc];
}

static annotation_byte_code_t bc_check_valid_top_level(annotation_byte_code_t bc) {
  if (!(   (START_VAL < bc && bc < END_VAL)
        || (START_FUNC < bc && bc < END_FUNC)
        || (START_GOAL < bc && bc < END_GOAL))) {
        FPRINTF_TO_ERR_FILE("invalid top level byte code value %d %s\n", bc, bc_str(bc));
        raise(SIGSTOP);
        _exit(1);
      }
  return bc;
}

static annotation_byte_code_t bc_check_valid(annotation_byte_code_t bc) {
  if (bc >= MAX_BYTE_CODE || bc < 0) {
      FPRINTF_TO_ERR_FILE("invalid byte code value %d\n", bc);
      raise(SIGSTOP);
      _exit(1);
  }
  return bc;
}

#define BC_STR(E) \
    annotation_byte_code_strings[E]

#define MAX_INSTRUCTION_SIZE 16

typedef struct annotation annotation_t;

typedef struct action {
  uint8_t * pos;
  uint8_t instruction_size;
  char instruction_bytes[MAX_INSTRUCTION_SIZE];
  int byte_code_len;
  annotation_byte_code_t * byte_code;
  struct action * annotation_next;
  struct action * pos_next;
  annotation_t * annotation;
} action_t;

typedef struct annotation {
  int id;
  int shm_id;
  shm_content_t * shm_addr;
  action_t * actions;
  UT_hash_handle hh;
  UT_hash_handle hh_active;
} annotation_t;

typedef struct {
  void * pos;
  action_t * actions;
  UT_hash_handle hh;
} pos_actions_t;

static annotation_t * annotations_map = NULL;
static annotation_t * active_annotations_map = NULL;
static pos_actions_t * pos_actions_map = NULL;

static __thread uint8_t * single_step_start_pos = NULL;
static __thread action_t * edge_cov_action = NULL;
static __thread uint64_t edge_cov_target = 0;

static void set_breakpoint(action_t * action, int quiet) {
  if (!(*action->pos == 0xCC || *action->pos == (uint8_t)action->instruction_bytes[0])) {
      FPRINTF_TO_ERR_FILE("set bp pos (%p) is not 0xCC or expected initial 0x%x but 0x%x\n",
      action->pos, (uint8_t)action->instruction_bytes[0], *action->pos);
      raise(SIGSTOP);
      _exit(1);
  }
  if (!quiet) {
    FPRINTF_TO_ERR_FILE("setting breakpoint at %p\n", action->pos);
  }

  uint8_t* base = action->pos - ((uint64_t)action->pos)%4096;
  // TODO find initial protections to restore them
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_WRITE|PROT_EXEC )==0);
  *(uint8_t*)action->pos = 0xcc;
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_EXEC )==0);
}

static void set_breakpoint_at_addr(uint8_t * addr) {
  uint8_t* base = addr - ((uint64_t)addr)%4096;
  // TODO find initial protections to restore them
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_WRITE|PROT_EXEC )==0);
  *(uint8_t*)addr = 0xcc;
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_EXEC )==0);
}


static void remove_breakpoint(action_t * action, int quiet) {
  if (!(*action->pos == 0xcc || *action->pos == (uint8_t)action->instruction_bytes[0])) {
      FPRINTF_TO_ERR_FILE("remove bp pos (%lx) is not 0xcc or expected initial 0x%x but 0x%x\n",
      action->pos, (uint8_t)action->instruction_bytes[0], *action->pos);
      raise(SIGSTOP);
      _exit(1);
  }
  if (!quiet) {
    FPRINTF_TO_ERR_FILE("removing breakpoint at %p\n", action->pos);
  }

  uint8_t* base = action->pos - ((uint64_t)action->pos)%4096;
  // TODO find initial protections to restore them
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_WRITE|PROT_EXEC )==0);
  *(uint8_t*)action->pos = (uint8_t)action->instruction_bytes[0];
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_EXEC )==0);
}

#define CHECK_BIT(var,pos) (!!((var) & (pos)))

#define REGISTER_LOWER(val) (val & 0xFF)
#define REGISTER_HIGHER(val) (val & 0xFF00)
#define REGISTER_16BIT(val) (val & 0xFFFF)
#define REGISTER_EXTENDED(val) (val & 0xFFFFFFFF)

#define CLASSIC_REGISTER_CASES(NAME) \
  case R##NAME##X: \
    return ctx->uc_mcontext.gregs[REG_R##NAME##X]; \
  case E##NAME##X: \
    return REGISTER_EXTENDED(ctx->uc_mcontext.gregs[REG_R##NAME##X]); \
  case NAME##X: \
    return REGISTER_16BIT(ctx->uc_mcontext.gregs[REG_R##NAME##X]); \
  case NAME##H: \
    return REGISTER_HIGHER(ctx->uc_mcontext.gregs[REG_R##NAME##X]); \
  case NAME##L: \
    return REGISTER_LOWER(ctx->uc_mcontext.gregs[REG_R##NAME##X]);

#define SOURCE_DEST_REGISTER_CASES(NAME) \
  case R##NAME##I: \
    return ctx->uc_mcontext.gregs[REG_R##NAME##I]; \
  case E##NAME##I: \
    return REGISTER_EXTENDED(ctx->uc_mcontext.gregs[REG_R##NAME##I]); \
  case NAME##I: \
    return REGISTER_16BIT(ctx->uc_mcontext.gregs[REG_R##NAME##I]); \
  case NAME##IL: \
    return REGISTER_LOWER(ctx->uc_mcontext.gregs[REG_R##NAME##I]);

#define P_REGISTER_CASES(NAME) \
  case R##NAME##P: \
    return ctx->uc_mcontext.gregs[REG_R##NAME##P]; \
  case E##NAME##P: \
    return REGISTER_EXTENDED(ctx->uc_mcontext.gregs[REG_R##NAME##P]); \
  case NAME##P: \
    return REGISTER_16BIT(ctx->uc_mcontext.gregs[REG_R##NAME##P]); \
  case NAME##PL: \
    return REGISTER_LOWER(ctx->uc_mcontext.gregs[REG_R##NAME##P]);

#define P_WITHOUT_L_REGISTER_CASES(NAME) \
  case R##NAME##P: \
    return ctx->uc_mcontext.gregs[REG_R##NAME##P]; \
  case E##NAME##P: \
    return REGISTER_EXTENDED(ctx->uc_mcontext.gregs[REG_R##NAME##P]); \
  case NAME##P: \
    return REGISTER_16BIT(ctx->uc_mcontext.gregs[REG_R##NAME##P]);

#define NEW_REGISTER_CASES(NAME) \
  case R##NAME: \
    return ctx->uc_mcontext.gregs[REG_R##NAME]; \
  case R##NAME##D: \
    return REGISTER_EXTENDED(ctx->uc_mcontext.gregs[REG_R##NAME]); \
  case R##NAME##W: \
    return REGISTER_16BIT(ctx->uc_mcontext.gregs[REG_R##NAME]); \
  case R##NAME##B: \
    return REGISTER_LOWER(ctx->uc_mcontext.gregs[REG_R##NAME]);

#define BC_MAX_STACK 64

#define BC_PUSH(V) \
  if (stack_ptr >= stack + 64) { \
      FPRINTF_TO_ERR_FILE("bc stack overflow %s:%d\n", __FILE__, __LINE__); \
      raise(SIGSTOP); \
      _exit(1); \
  } \
  *stack_ptr = V; \
  stack_ptr += 1;

#define BC_POP(V) \
  stack_ptr -= 1; \
  if (stack_ptr < stack) { \
    FPRINTF_TO_ERR_FILE("bc stack underflow %s:%d\n", __FILE__, __LINE__); \
    raise(SIGSTOP); \
    _exit(1); \
  } \
  V = *stack_ptr;

#define BC_PEEK(V) \
  if (stack_ptr-1 < stack) { \
    FPRINTF_TO_ERR_FILE("bc stack underflow %s:%d\n", __FILE__, __LINE__); \
    raise(SIGSTOP); \
    _exit(1); \
  } \
  V = *(stack_ptr-1);

#define BC_PRINT_STACK() \
  uint64_t * p = stack_ptr; \
  FPRINTF_TO_ERR_FILE("^^^^^^^^^\n");  \
  while (--p >= stack) { \
    FPRINTF_TO_ERR_FILE("%p\t0x%x | %d\n", p, *p, *p);  \
  } \
  FPRINTF_TO_ERR_FILE("=========\n");


static uint64_t bc_get_reg(annotation_byte_code_t reg, ucontext_t * ctx, int allow_no_reg,
                    int verbose) {
  if (verbose) { FPRINTF_TO_ERR_FILE("register: %s(%d)\n", bc_str(reg), reg); }
  switch(reg) {
    case NO_REG:
      if (allow_no_reg) {
        return 0;
      }
      FPRINTF_TO_ERR_FILE("no_reg is not allowed: %s(%d) ", bc_str(reg), reg);
      raise(SIGSTOP);
      _exit(1);
    // I'm sorry ... (using macros should hopefully reduce the chance for typos)
    CLASSIC_REGISTER_CASES(A);
    CLASSIC_REGISTER_CASES(B);
    CLASSIC_REGISTER_CASES(C);
    CLASSIC_REGISTER_CASES(D);
    SOURCE_DEST_REGISTER_CASES(S);
    SOURCE_DEST_REGISTER_CASES(D);
    NEW_REGISTER_CASES(8);
    NEW_REGISTER_CASES(9);
    NEW_REGISTER_CASES(10);
    NEW_REGISTER_CASES(11);
    NEW_REGISTER_CASES(12);
    NEW_REGISTER_CASES(13);
    NEW_REGISTER_CASES(14);
    NEW_REGISTER_CASES(15);
    P_REGISTER_CASES(B);
    P_REGISTER_CASES(S);
    P_WITHOUT_L_REGISTER_CASES(I);
    case CS:
      return  ctx->uc_mcontext.gregs[REG_CSGSFS]        & 0xFFFF;
    case FS:
      return (ctx->uc_mcontext.gregs[REG_CSGSFS] >> 16) & 0xFFFF;
    case GS:
      return (ctx->uc_mcontext.gregs[REG_CSGSFS] >> 32) & 0xFFFF;
    default:
      FPRINTF_TO_ERR_FILE("ERROR unhandled reg: %s(%d)\n", bc_str(reg), reg);
      raise(SIGSTOP);
      _exit(1);
  }
}

static uint64_t bc_get_ptr(annotation_byte_code_t segment_reg,
                    annotation_byte_code_t base_reg,
                    annotation_byte_code_t index_reg,
                    uint64_t scale,
                    annotation_byte_code_t disp_type,
                    uint64_t displacement,
                    uint64_t size,
                    ucontext_t * ctx,
                    int verbose) {
  uint64_t segment = bc_get_reg(segment_reg, ctx, /* allow no_reg */ 1, verbose);
  uint64_t base = bc_get_reg(base_reg, ctx, /* allow no_reg */ 1, verbose);
  uint64_t index = bc_get_reg(index_reg, ctx, /* allow no_reg */ 1, verbose);
  uint64_t addr = 0;
  if (disp_type == DISP_POS) {
    addr = segment + base + index*scale + displacement;
  } else if (disp_type == DISP_NEG) {
    addr = segment + base + index*scale + (int32_t)displacement;
  } else {
    FPRINTF_TO_ERR_FILE("ERROR invalid disp type %d", disp_type);
    raise(SIGSTOP);
    _exit(1);
  }
  if (verbose) { FPRINTF_TO_ERR_FILE("addr: %p + %p + %d*%d + %d = %p size:(%d)\n",
                 segment, base, index, scale, displacement, addr, size); }
  return addr;
}

static bool is_pointer_valid(uint64_t p, int verbose) {
    /* get the page size */
    size_t page_size = sysconf(_SC_PAGESIZE);
    /* find the address of the page that contains p */
    void *base = (void *)((((size_t)p) / page_size) * page_size);
    /* call msync, if it returns non-zero, return false */
    if (msync(base, page_size, MS_ASYNC) == 0) {
      if (verbose) { FPRINTF_TO_ERR_FILE("valid ptr: %p\n", p); }
      return 1;
    } else {
      if (errno == ENOMEM) {
        if (verbose) { FPRINTF_TO_ERR_FILE("invalid ptr: %p\n", p); }
        return 0;
      } else {
        FPRINTF_TO_ERR_FILE("ERROR during msync of %p: %s\n", p, strerror(errno));
        raise(SIGSTOP);
        _exit(1);
      }
    }
}
  
static uint64_t bc_get_mem(annotation_byte_code_t segment_reg,
                    annotation_byte_code_t base_reg,
                    annotation_byte_code_t index_reg,
                    uint64_t scale,
                    annotation_byte_code_t disp_type,
                    uint64_t displacement,
                    uint64_t size,
                    ucontext_t * ctx,
                    int verbose) {
  uint64_t addr = bc_get_ptr(segment_reg, base_reg, index_reg, scale, disp_type, displacement, size, ctx, verbose);
  if (is_pointer_valid(addr, verbose)) {
    uint64_t res = 0;
    switch(size) {
      case 8:
        res = *(uint64_t*)addr;
        break;
      case 4:
        res = *(uint32_t*)addr;
        break;
      case 2:
        res = *(uint16_t*)addr;
        break;
      case 1:
        res = *(uint8_t*)addr;
        break;
    }
    if (verbose) { FPRINTF_TO_ERR_FILE("mem: %x %d @ addr: %p (%d)\n", res, res, addr, size); }
    return res;
  } else {
    FPRINTF_TO_ERR_FILE("ptr is invalid can't read memory: %p\n", addr);
    return 0;
  }
}

static void set_bit_in_hashmap(uint64_t x, shm_content_t * shm, int verbose) {
  uint8_t * annotation_res = shm->result.set_hash_map;

  if (verbose) { FPRINTF_TO_ERR_FILE("num write: %d ", shm->num_writes_during_run); }
  if (verbose) { FPRINTF_TO_ERR_FILE("val: %llx ", x); }

  // hash it
  x = (x ^ (x >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  x = (x ^ (x >> 27)) * UINT64_C(0x94d049bb133111eb);
  x = x ^ (x >> 31);

  if (verbose) { FPRINTF_TO_ERR_FILE("hashed: %llx ", x); }

  x = x % (sizeof(shm->result.set_hash_map)*8);
  if (verbose) { FPRINTF_TO_ERR_FILE("comp: %llx ", x); }

  int byte_offset = x/8;
  int bit_offset = x%8;
  if (verbose) { FPRINTF_TO_ERR_FILE("byte_off: %d bit_off: %d\n", byte_offset, bit_offset); }

  annotation_res[byte_offset] |= (1 << (bit_offset));

  shm->num_writes_during_run++;
}

static void exec_annotation(annotation_byte_code_t * byte_code, int byte_code_len,
                     ucontext_t * ctx, action_t * action, int verbose) {
  uint64_t i = 0;
  uint64_t stack[BC_MAX_STACK];
  uint64_t * stack_ptr = stack;
  if (verbose) { FPRINTF_TO_ERR_FILE("\nexec(%d): \n", byte_code_len); }
  while (i < byte_code_len) {
    if (verbose) { FPRINTF_TO_ERR_FILE("inst: %s(%d)\n", bc_str(byte_code[i]), byte_code[i]); }
    switch(bc_check_valid_top_level(byte_code[i++])) {
      case VAL_IMM:
        if (verbose) { FPRINTF_TO_ERR_FILE("imm: %x | %d\n", byte_code[i], byte_code[i]); };
        BC_PUSH(byte_code[i++]);
        break;
      case VAL_REG:
        BC_PUSH(bc_get_reg(bc_check_valid(byte_code[i++]), ctx, /* allow no_reg */ 0, verbose));
        break;
      case VAL_MEM:
        {
          annotation_byte_code_t segment_reg = byte_code[i++];
          annotation_byte_code_t base_reg = byte_code[i++];
          annotation_byte_code_t index_reg = byte_code[i++];
          uint64_t scale = byte_code[i++];
          annotation_byte_code_t disp_type = byte_code[i++];
          uint64_t displacement = byte_code[i++];
          uint64_t size = byte_code[i++];
          BC_PUSH(bc_get_mem(segment_reg, base_reg, index_reg, scale, disp_type, displacement, size,
                             ctx, verbose));
        }
        break;
      case VAL_PTR:
        {
          annotation_byte_code_t segment_reg = byte_code[i++];
          annotation_byte_code_t base_reg = byte_code[i++];
          annotation_byte_code_t index_reg = byte_code[i++];
          uint64_t scale = byte_code[i++];
          annotation_byte_code_t disp_type = byte_code[i++];
          uint64_t displacement = byte_code[i++];
          uint64_t size = byte_code[i++];
          BC_PUSH(bc_get_ptr(segment_reg, base_reg, index_reg, scale, disp_type, displacement, size,
                             ctx, verbose));
        }
        break;
      case CALC_SUB:
        {
          uint64_t a, b;
          BC_POP(a);
          BC_POP(b);
          BC_PUSH(a - b);
        }
        break;
      case CALC_ABS:
        {
          int64_t val;
          BC_POP(val);
          val = labs(val);
          BC_PUSH(val);
        }
        break;
      case CALC_HAMMING:
        {
          uint64_t a, b;
          BC_POP(a);
          BC_POP(b);
          BC_PUSH(__builtin_popcountll(a ^ b));
        }
        break;
      case CALC_HAMMING_FOR:
        {
          uint64_t size, a_ptr, b_ptr, total = 0;
          BC_POP(size);
          BC_POP(a_ptr);
          BC_POP(b_ptr);
          if (verbose) { FPRINTF_TO_ERR_FILE("size: %d\n", size); }
          if (is_pointer_valid(a_ptr, verbose) && is_pointer_valid(b_ptr, verbose)) {
            for (int i = 0; i < size; i++) {
              int a_val = *(uint8_t*)(a_ptr+i);
              int b_val = *(uint8_t*)(b_ptr+i);
              total += __builtin_popcount(a_val ^ b_val);
              if (verbose) { FPRINTF_TO_ERR_FILE("pos: %p %x ^ %x -> %d\n", i, a_val, b_val, total); }
            }
          }
          BC_PUSH(total);
        }
        break;
      case GOAL_MIN:
      case GOAL_MAX: // comparison is done in fuzzer code
        {
          // TODO this is not thread safe
          annotation_t * annotation = action->annotation;
          NULL_CHECK(annotation->shm_addr);
          shm_content_t * shm = annotation->shm_addr;
          uint64_t res;
          if (shm->num_writes_during_run >= ANNOTATION_RESULT_SIZE) {
            break; // pos is too high
          }
          BC_PEEK(res);
          shm->result.best_values[shm->num_writes_during_run] = res;
          shm->num_writes_during_run++;
        }
        break;
      case GOAL_SET:
        {
          annotation_t * annotation = action->annotation;
          NULL_CHECK(annotation->shm_addr);
          shm_content_t * shm = annotation->shm_addr;
          uint64_t x;
          BC_PEEK(x);
          set_bit_in_hashmap(x, shm, verbose);
        }
        break;
      case GOAL_EDGE_COV:
        {
          uint64_t target;
          BC_PEEK(target);
          edge_cov_target = target;
          edge_cov_action = action;
        }
        break;
      case GOAL_EDGE_MEM_COV:
        {
          edge_cov_target = 0;  // In band signal for unknown targets, new ones are important.
          edge_cov_action = action;
        }
        break;
      default:
        FPRINTF_TO_ERR_FILE("unhandled bc: %s(%d) \n", bc_str(byte_code[i-1]), byte_code[i-1]);
        return;
    }
    if (verbose) { BC_PRINT_STACK(); }
  }
}

static void sigtrap_handler(int signo, siginfo_t *si, void* arg)
{
  assert(signo == SIGTRAP);
  ucontext_t *ctx = (ucontext_t *)arg;
  if (single_step_start_pos == NULL) {
    // we only expect to land here if we set a bp, a bp (0xcc / int 3) is one byte long
    // and instructions are completed before we get to the signal handler
    // so subtract one from our position
    uint8_t * pos = (uint8_t *)ctx->uc_mcontext.gregs[REG_RIP] - 1;

    pos_actions_t * actions;
    HASH_FIND_PTR(pos_actions_map, &pos, actions);
    if (actions) {
      action_t * act = actions->actions;
      LL_FOREACH2(actions->actions, act, pos_next) {
        int verbose = act->pos == (uint8_t*)0x0; // for debugging purposes
        if (verbose) { FPRINTF_TO_ERR_FILE("Execution annotations for %p\n", act->pos); }
        exec_annotation(act->byte_code, act->byte_code_len, ctx, act, verbose);
      }

      act = actions->actions;

      // restore old instruction and single step once then we can get the result
      single_step_start_pos = pos;
      
      // set trap flag to start single stepping
      ctx->uc_mcontext.gregs[REG_EFL] |= 0x100;

      // set RIP so that instruction is repeated
      // TODO displaced stepping or emulate instruction -> to make this thread safe
      ctx->uc_mcontext.gregs[REG_RIP] -= 1;

      remove_breakpoint(act, /*quiet*/ 1);
    } else {
      FPRINTF_TO_ERR_FILE("ERROR no actions for %p found (before stepping)\n", pos);
      raise(SIGSTOP);
      _exit(1);
    }
    return;
  } else {

    // const uint8_t * pos = (uint8_t *)ctx->uc_mcontext.gregs[REG_RIP] - single_step_size;
    // pos_actions_t * actions;
    // HASH_FIND_PTR(pos_actions_map, &pos, actions);
    // if (actions) {
    //   action_t * act = actions->actions;
    //   set_breakpoint(act, /*quiet*/ 1);
    // } else {
    //   FPRINTF_TO_ERR_FILE("no actions for %p found (after stepping %d - real pos %p)\n",
    //           pos, single_step_size, (uint8_t *)ctx->uc_mcontext.gregs[REG_RIP]);
    // }
    set_breakpoint_at_addr(single_step_start_pos);

    // unset trap flag
    ctx->uc_mcontext.gregs[REG_EFL] &= ~0x100;

    single_step_start_pos = NULL;

    if (edge_cov_action != NULL) {
      uint8_t * pos = (uint8_t *)ctx->uc_mcontext.gregs[REG_RIP];
      if (edge_cov_target == 0) {
        annotation_t * annotation = edge_cov_action->annotation;
        NULL_CHECK(annotation->shm_addr);
        shm_content_t * shm = annotation->shm_addr;
        set_bit_in_hashmap((uint64_t)pos, shm, 0);
      } else {
        if ((uint64_t)pos == edge_cov_target) {
          annotation_t * annotation = edge_cov_action->annotation;
          NULL_CHECK(annotation->shm_addr);
          shm_content_t * shm = annotation->shm_addr;
          shm->num_writes_during_run = 1;
        }
      }

      edge_cov_action = NULL;
      edge_cov_target = 0;
    }
  }
}

void backtrace_handler(int sig, siginfo_t *si, void* arg) {
  void *array[256];
  size_t size;

  // get void*'s for all entries on the stack
  size = backtrace(array, 256);

  // print out all the frames to stderr
  FPRINTF_TO_ERR_FILE("Error: signal %d:\n", sig);

  if (put_err_log_fp != NULL) {
    backtrace_symbols_fd(array, size, fileno(put_err_log_fp));
  } else {
    backtrace_symbols_fd(array, size, STDERR_FILENO);
  }

  ucontext_t *ctx = (ucontext_t *)arg;
  uint8_t * pos = (uint8_t *)ctx->uc_mcontext.gregs[REG_RIP] - 16;

  FPRINTF_TO_ERR_FILE("\ncode around %p: ", pos+16);
  int i;
  for (i = 0; i < 32; i++)
  {
      if (i > 0) FPRINTF_TO_ERR_FILE(":");
      FPRINTF_TO_ERR_FILE("%02X", pos[i]);
  }
  FPRINTF_TO_ERR_FILE("\n");

  char done_msg[4] = "WHAT";
  WRITE_TO_COMMAND_PIPE(&done_msg, 4);
  raise(SIGSTOP);
  return;
}

static void print_annotations() {
  annotation_t * an;
  action_t * ac;
  char msg [4096];
  char *cur = msg, * const end = msg + sizeof(msg);
  cur += snprintf(cur, end-cur, "there are %d annotations, %d actions: ",
          HASH_COUNT(annotations_map), HASH_COUNT(pos_actions_map));
  for (an=annotations_map; an != NULL; an=an->hh.next) {
    if (cur >= end) break;
    cur += snprintf(cur, end-cur, "\n\t%d (", an->id);
    LL_FOREACH2(an->actions, ac, annotation_next) {
      if (cur >= end) break;
      cur += snprintf(cur, end-cur, "%p, ", ac->pos);
    }
    if (cur >= end) break;
    cur += snprintf(cur, end-cur, ") ");
  }
  if (cur > end) {
    *end = '\0';
  } else {
    *cur = '\0';
  }
  FPRINTF_TO_ERR_FILE("%s\n", msg);
}

static void handle_bb_req() {
  struct BBReq req;
  READ_FROM_COMMAND_PIPE(req);

  annotation_t * ann = NULL, * tmp_ann = NULL;
  action_t * act = NULL;
  HASH_ITER(hh_active, active_annotations_map, ann, tmp_ann) {
    LL_FOREACH2(ann->actions, act, annotation_next) {
      // TODO remove message
      if ((uint64_t)req.pos <= (uint64_t)act->pos && (uint64_t)act->pos < ((uint64_t)req.pos+req.size)) {
        FPRINTF_TO_ERR_FILE("would have gotten the wrong value %x in %x %d\n", act->pos, req.pos, req.size);
      }
      remove_breakpoint(act, /*quiet*/ 1);
    }
  }

  WRITE_TO_COMMAND_PIPE(req.pos, req.size);

  HASH_ITER(hh_active, active_annotations_map, ann, tmp_ann) {
    LL_FOREACH2(ann->actions, act, annotation_next) {
      set_breakpoint(act, /*quiet*/ 1);
    }
  }
}

static void remove_annotation(int annotation_id) {
  // find annotation
  annotation_t * annotation;
  HASH_FIND_INT(annotations_map, &annotation_id, annotation);
  if (annotation == NULL) {
      FPRINTF_TO_ERR_FILE("expected annotation for %d to exist\n", annotation_id);
      raise(SIGSTOP);
      _exit(1);
  }

  annotation_t * active_ann;
  HASH_FIND(hh_active, active_annotations_map, &annotation->id, sizeof(int), active_ann);
  if (active_ann != NULL) {
    HASH_DELETE(hh_active, active_annotations_map, annotation);
  }

  // for all actions belonging to annotation find them and remove them
  action_t * el = NULL;
  action_t * tmp = NULL;
  LL_FOREACH_SAFE2(annotation->actions, el, tmp, annotation_next) {
    LL_DELETE2(annotation->actions, el, annotation_next);
    pos_actions_t * pos_action;
    HASH_FIND_PTR(pos_actions_map, &el->pos, pos_action);
    if (!pos_action) {
      FPRINTF_TO_ERR_FILE("expected pos_action for %p to exist\n", el->pos);
    }
    LL_DELETE2(pos_action->actions, el, pos_next);
    action_t * count_el = NULL;
    int count = -1;
    LL_COUNT2(pos_action->actions, count_el, count, pos_next);
    if (count == 0) {
      HASH_DEL(pos_actions_map, pos_action);
      free(pos_action);

      // remove breakpoint
      remove_breakpoint(el, /*quiet*/ 1);
    }
    free(el->byte_code);
    free(el);
  }

  // remove annotation annotation
  shmdt(annotation->shm_addr);
  annotation->shm_addr = NULL;
  HASH_DEL(annotations_map, annotation);
  free(annotation);

  // print_annotations();
}

static void handle_ann_req(void) {
  // get annotation
  annotation_t * ann = calloc(1, sizeof(*ann));
  NULL_CHECK(ann);
  ann->actions = NULL;
  READ_FROM_COMMAND_PIPE(ann->id);
  READ_FROM_COMMAND_PIPE(ann->shm_id);
  ann->shm_addr = shmat(ann->shm_id, NULL, 0);
  if (ann->shm_addr == (void *) -1) {
    perror("could not get shm segment");
    raise(SIGSTOP);
    _exit(1);
  }
  HASH_ADD_INT(annotations_map, id, ann);

  {
    annotation_t * active_ann;
    HASH_FIND(hh_active, active_annotations_map, &ann->id, sizeof(int), active_ann);
    if (active_ann == NULL) {
      HASH_ADD(hh_active, active_annotations_map, id, sizeof(int), ann);
    }
  }

  // get all actions for that bb_annotation
  while (1) {
    uint8_t * action_pos = 0;
    READ_FROM_COMMAND_PIPE(action_pos);
    if (action_pos == NULL) {
      break;
    }

    action_t * action = calloc(1, sizeof(*action));
    NULL_CHECK(action);
    action->pos = action_pos;
    READ_FROM_COMMAND_PIPE(action->instruction_size);
    READ_FROM_COMMAND_PIPE2(&action->instruction_bytes, action->instruction_size);
    READ_FROM_COMMAND_PIPE(action->byte_code_len);
    annotation_byte_code_t * action_byte_code = calloc(action->byte_code_len, sizeof(*action_byte_code));
    NULL_CHECK(action_byte_code);
    int i = 0;
    while (i < action->byte_code_len) {
      READ_FROM_COMMAND_PIPE2(&(action_byte_code[i++]), sizeof(*action_byte_code));
    }
    action->byte_code = action_byte_code;
    action->annotation = ann;
    action->annotation_next = NULL;
    action->pos_next = NULL;

    // get action list for position
    pos_actions_t * pos_actions;
    HASH_FIND_PTR(pos_actions_map, &action->pos, pos_actions);

    // if action list does not exist -> create it
    if (pos_actions == NULL) {
      pos_actions = calloc(1, sizeof(*pos_actions));
      NULL_CHECK(pos_actions);
      pos_actions->pos = action->pos;
      pos_actions->actions = NULL;
      HASH_ADD_PTR(pos_actions_map, pos, pos_actions);
    }

    // insert action struct
    LL_PREPEND2(pos_actions->actions, action, pos_next);
    LL_PREPEND2(ann->actions, action, annotation_next);

    // set breakpoint to enable action
    set_breakpoint(action, /*quiet*/ 1);
  }

  // print_annotations();
}

static void handle_deann_req(void) {
  int id = 0;
  READ_FROM_COMMAND_PIPE(id);
  remove_annotation(id);
  // TODO return command success?
}

static void handle_activate_annotation() {
  int id = -1;
  READ_FROM_COMMAND_PIPE(id);
  annotation_t * annotation;
  HASH_FIND_INT(annotations_map, &id, annotation);
  NULL_CHECK(annotation);

  annotation_t * active_ann;
  HASH_FIND(hh_active, active_annotations_map, &id, sizeof(int), active_ann);
  if (active_ann == NULL) {
    HASH_ADD(hh_active, active_annotations_map, id, sizeof(int), annotation);
  }

  action_t * act = NULL;
  LL_FOREACH2(annotation->actions, act, annotation_next) {
      set_breakpoint(act, /*quiet*/ 1);
  }
}

static void handle_deactivate_annotation() {
  int id = -1;
  READ_FROM_COMMAND_PIPE(id);
  annotation_t * annotation;
  HASH_FIND_INT(annotations_map, &id, annotation);
  NULL_CHECK(annotation);

  annotation_t * active_ann;
  HASH_FIND(hh_active, active_annotations_map, &id, sizeof(int), active_ann);
  if (active_ann != NULL) {
    annotation->shm_addr->num_writes_during_run = 0;
    HASH_DELETE(hh_active, active_annotations_map, active_ann);
  }

  action_t * act = NULL;
  LL_FOREACH2(annotation->actions, act, annotation_next) {
      remove_breakpoint(act, /*quiet*/ 1);
  }
}


/* Fork server logic. */

static void __afl_start_forkserver(void) {

#ifdef __linux__
  if (!is_persistent && !__afl_cmp_map && !getenv("AFL_NO_SNAPSHOT") &&
      afl_snapshot_init() >= 0) {

    __afl_start_snapshots();
    return;

  }

#endif

  u8  tmp[4] = {0, 0, 0, 0};
  s32 child_pid;
  u32 status = 0;
  u32 already_read_first = 0;
  u32 was_killed;

  u8 child_stopped = 0;

  void (*old_sigchld_handler)(int) = 0;  // = signal(SIGCHLD, SIG_DFL);

  if (__afl_map_size <= FS_OPT_MAX_MAPSIZE)
    status |= (FS_OPT_SET_MAPSIZE(__afl_map_size) | FS_OPT_MAPSIZE);
  if (__afl_dictionary_len > 0 && __afl_dictionary) status |= FS_OPT_AUTODICT;
  if (status) status |= (FS_OPT_ENABLED);
  memcpy(tmp, &status, 4);

  /* Phone home and tell the parent that we're OK. If parent isn't there,
     assume we're not running in forkserver mode and just execute program. */

  if (write(FORKSRV_FD + 1, tmp, 4) != 4) return;
  {
    struct sigaction action;
    action.sa_sigaction = &sigtrap_handler;
    action.sa_flags = SA_SIGINFO;
    sigaction(SIGTRAP, &action, NULL);
  }

  char * put_log_path = getenv("IJON_PUT_LOG_PATH");
  if (put_log_path == NULL) {
    fprintf(stderr, "Got no IJON_PUT_LOG_PATH will log to stderr\n");
  } else {
    if ((put_err_log_fp = fopen(put_log_path, "a")) == NULL) {
      fprintf(stderr, "Can't open error log file: %s\n", strerror(errno));
    } else {
    }
  }
  FPRINTF_TO_ERR_FILE("PUT starting up\n");

  {
    struct sigaction action;
    action.sa_sigaction = &backtrace_handler;
    action.sa_flags = SA_SIGINFO | SA_RESETHAND;
    sigaction(SIGSEGV, &action, NULL);
    sigaction(SIGILL, &action, NULL);
    sigaction(SIGFPE, &action, NULL);
    sigaction(SIGBUS, &action, NULL);
    sigaction(SIGABRT, &action, NULL);
  }

  if (__afl_dictionary_len > 0 && __afl_dictionary) {

    if (read(FORKSRV_FD, &was_killed, 4) != 4) _exit(1);

    if ((was_killed & (FS_OPT_ENABLED | FS_OPT_AUTODICT)) ==
        (FS_OPT_ENABLED | FS_OPT_AUTODICT)) {

      // great lets pass the dictionary through the forkserver FD
      u32 len = __afl_dictionary_len, offset = 0;
      s32 ret;

      if (write(FORKSRV_FD + 1, &len, 4) != 4) {

        write(2, "Error: could not send dictionary len\n",
              strlen("Error: could not send dictionary len\n"));
        _exit(1);

      }

      while (len != 0) {

        ret = write(FORKSRV_FD + 1, __afl_dictionary + offset, len);

        if (ret < 1) {

          write(2, "Error: could not send dictionary\n",
                strlen("Error: could not send dictionary\n"));
          _exit(1);

        }

        len -= ret;
        offset += ret;

      }

    } else {

      // uh this forkserver master does not understand extended option passing
      // or does not want the dictionary
      already_read_first = 1;

    }

  }

  while (1) {

    fd_set rfds;
    u32 was_killed;
    int status;

    /* Wait for parent by reading from the pipe. Abort if read fails. */
    FD_ZERO(&rfds);
    FD_SET(FORKSRV_FD, &rfds);
    FD_SET(FORKSRV_FD + 2, &rfds);
    if (select(FORKSRV_FD + 2 + 1, &rfds, NULL, NULL, NULL) == -1) {
      perror("select()");
    }

    // Received a command and not a request to fuzz
    if (FD_ISSET(FORKSRV_FD + 2, &rfds)) {
      int err = 0;
      char cmd[4] = {0};
      READ_FROM_COMMAND_PIPE__BASE(err, cmd, sizeof(cmd));
      if (err) {
        char done_msg[4] = "WHAT";
        WRITE_TO_COMMAND_PIPE(&done_msg, 4);
        raise(SIGSTOP);
        abort();
      }
      if (strncmp("A_AN", cmd, 4) == 0) {
        handle_activate_annotation();
      } else if (strncmp("D_AN", cmd, 4) == 0) {
        handle_deactivate_annotation();
      } else if (strncmp("BB_R", cmd, 4) == 0) {
        handle_bb_req();
      } else if (strncmp("EANR", cmd, 4) == 0) {
        handle_ann_req();
      } else if (strncmp("DANR", cmd, 4) == 0) {
        handle_deann_req();
      } else {
        FPRINTF_TO_ERR_FILE("fuzzee unknown command: %s\n", cmd);
      }
      char done_msg[4] = "DONE";
      WRITE_TO_COMMAND_PIPE(&done_msg, 4);
      continue;
    }

    if (already_read_first) {

      already_read_first = 0;

    } else {

      if (read(FORKSRV_FD, &was_killed, 4) != 4) _exit(1);

    }

    /* If we stopped the child in persistent mode, but there was a race
       condition and afl-fuzz already issued SIGKILL, write off the old
       process. */

    if (child_stopped && was_killed) {

      child_stopped = 0;
      if (waitpid(child_pid, &status, 0) < 0) _exit(1);

    }

    if (!child_stopped) {

      /* Once woken up, create a clone of our process and reset annotations. */

      {
        annotation_t * ann, * tmp_ann;
        HASH_ITER(hh_active, active_annotations_map, ann, tmp_ann) {
          ann->shm_addr->num_writes_during_run = 0;
        }
      }

      child_pid = fork();
      if (child_pid < 0) _exit(1);

      /* In child process: close fds, resume execution. */

      if (!child_pid) {

        signal(SIGCHLD, old_sigchld_handler);

        close(FORKSRV_FD);
        close(FORKSRV_FD + 1);
        close(FORKSRV_FD + 2);
        close(FORKSRV_FD + 3);
        return;

      }

    } else {

      /* Special handling for persistent mode: if the child is alive but
         currently stopped, simply restart it with SIGCONT. */

      kill(child_pid, SIGCONT);
      child_stopped = 0;

    }

    /* In parent process: write PID to pipe, then wait for child. */

    if (write(FORKSRV_FD + 1, &child_pid, 4) != 4) _exit(1);

    if (waitpid(child_pid, &status, is_persistent ? WUNTRACED : 0) < 0)
      _exit(1);

    /* In persistent mode, the child stops itself with SIGSTOP to indicate
       a successful run. In this case, we want to wake it up without forking
       again. */

    if (WIFSTOPPED(status)) child_stopped = 1;

    if (WIFSIGNALED(status)) {
      FPRINTF_TO_ERR_FILE("PUT signaled: %d, core: %d\n", WTERMSIG(status), WCOREDUMP(status));
    }

    if (WIFSTOPPED(status)) {
      FPRINTF_TO_ERR_FILE("PUT stopped: %d\n", WSTOPSIG(status));
    }

    if (WIFCONTINUED(status)) {
      FPRINTF_TO_ERR_FILE("PUT continued: %d\n");
    }

    /* Relay wait status to pipe, then loop back. */

    if (write(FORKSRV_FD + 1, &status, 4) != 4) _exit(1);

  }

}

/* A simplified persistent mode handler, used as explained in
 * llvm_mode/README.md. */

int __afl_persistent_loop(unsigned int max_cnt) {

  static u8  first_pass = 1;
  static u32 cycle_cnt;

  if (first_pass) {

    /* Make sure that every iteration of __AFL_LOOP() starts with a clean slate.
       On subsequent calls, the parent will take care of that, but on the first
       iteration, it's our job to erase any trace of whatever happened
       before the loop. */

    if (is_persistent) {

      memset(__afl_area_ptr, 0, __afl_map_size);
      __afl_area_ptr[0] = 1;
      memset(__afl_prev_loc, 0, NGRAM_SIZE_MAX * sizeof(PREV_LOC_T));

    }

    cycle_cnt = max_cnt;
    first_pass = 0;
    return 1;

  }

  if (is_persistent) {

    if (--cycle_cnt) {

      raise(SIGSTOP);

      __afl_area_ptr[0] = 1;
      memset(__afl_prev_loc, 0, NGRAM_SIZE_MAX * sizeof(PREV_LOC_T));

      return 1;

    } else {

      /* When exiting __AFL_LOOP(), make sure that the subsequent code that
         follows the loop is not traced. We do that by pivoting back to the
         dummy output region. */

      __afl_area_ptr = __afl_area_initial;

    }

  }

  return 0;

}

/* This one can be called from user code when deferred forkserver mode
    is enabled. */

void __afl_manual_init(void) {

  static u8 init_done;

  if (!init_done) {

    __afl_map_shm();
    __afl_start_forkserver();
    init_done = 1;

  }

}

/* Proper initialization routine. */

__attribute__((constructor(CONST_PRIO))) void __afl_auto_init(void) {

  is_persistent = !!getenv(PERSIST_ENV_VAR);

  if (getenv(DEFER_ENV_VAR)) return;

  __afl_manual_init();

}

/* The following stuff deals with supporting -fsanitize-coverage=trace-pc-guard.
   It remains non-operational in the traditional, plugin-backed LLVM mode.
   For more info about 'trace-pc-guard', see llvm_mode/README.md.

   The first function (__sanitizer_cov_trace_pc_guard) is called back on every
   edge (as opposed to every basic block). */

void __sanitizer_cov_trace_pc_guard(uint32_t *guard) {
  __afl_area_ptr[*guard]++;
}

/* Init callback. Populates instrumentation IDs. Note that we're using
   ID of 0 as a special value to indicate non-instrumented bits. That may
   still touch the bitmap, but in a fairly harmless way. */

void __sanitizer_cov_trace_pc_guard_init(uint32_t *start, uint32_t *stop) {

  u32 inst_ratio = 100;
  u8 *x;

  if (start == stop || *start) return;

  x = getenv("AFL_INST_RATIO");
  if (x) inst_ratio = atoi(x);

  if (!inst_ratio || inst_ratio > 100) {

    fprintf(stderr, "[-] ERROR: Invalid AFL_INST_RATIO (must be 1-100).\n");
    abort();

  }

  /* Make sure that the first element in the range is always set - we use that
     to avoid duplicate calls (which can happen as an artifact of the underlying
     implementation in LLVM). */

  *(start++) = R(MAP_SIZE - 1) + 1;

  while (start < stop) {

    if (R(100) < inst_ratio)
      *start = R(MAP_SIZE - 1) + 1;
    else
      *start = 0;

    start++;

  }

}

///// CmpLog instrumentation

void __cmplog_ins_hook1(uint8_t arg1, uint8_t arg2) {

  if (!__afl_cmp_map) return;

  uintptr_t k = (uintptr_t)__builtin_return_address(0);
  k = (k >> 4) ^ (k << 8);
  k &= CMP_MAP_W - 1;

  __afl_cmp_map->headers[k].type = CMP_TYPE_INS;

  u32 hits = __afl_cmp_map->headers[k].hits;
  __afl_cmp_map->headers[k].hits = hits + 1;
  // if (!__afl_cmp_map->headers[k].cnt)
  //  __afl_cmp_map->headers[k].cnt = __afl_cmp_counter++;

  __afl_cmp_map->headers[k].shape = 0;

  hits &= CMP_MAP_H - 1;
  __afl_cmp_map->log[k][hits].v0 = arg1;
  __afl_cmp_map->log[k][hits].v1 = arg2;

}

void __cmplog_ins_hook2(uint16_t arg1, uint16_t arg2) {

  if (!__afl_cmp_map) return;

  uintptr_t k = (uintptr_t)__builtin_return_address(0);
  k = (k >> 4) ^ (k << 8);
  k &= CMP_MAP_W - 1;

  __afl_cmp_map->headers[k].type = CMP_TYPE_INS;

  u32 hits = __afl_cmp_map->headers[k].hits;
  __afl_cmp_map->headers[k].hits = hits + 1;

  __afl_cmp_map->headers[k].shape = 1;

  hits &= CMP_MAP_H - 1;
  __afl_cmp_map->log[k][hits].v0 = arg1;
  __afl_cmp_map->log[k][hits].v1 = arg2;

}

void __cmplog_ins_hook4(uint32_t arg1, uint32_t arg2) {

  if (!__afl_cmp_map) return;

  uintptr_t k = (uintptr_t)__builtin_return_address(0);
  k = (k >> 4) ^ (k << 8);
  k &= CMP_MAP_W - 1;

  __afl_cmp_map->headers[k].type = CMP_TYPE_INS;

  u32 hits = __afl_cmp_map->headers[k].hits;
  __afl_cmp_map->headers[k].hits = hits + 1;

  __afl_cmp_map->headers[k].shape = 3;

  hits &= CMP_MAP_H - 1;
  __afl_cmp_map->log[k][hits].v0 = arg1;
  __afl_cmp_map->log[k][hits].v1 = arg2;

}

void __cmplog_ins_hook8(uint64_t arg1, uint64_t arg2) {

  if (!__afl_cmp_map) return;

  uintptr_t k = (uintptr_t)__builtin_return_address(0);
  k = (k >> 4) ^ (k << 8);
  k &= CMP_MAP_W - 1;

  __afl_cmp_map->headers[k].type = CMP_TYPE_INS;

  u32 hits = __afl_cmp_map->headers[k].hits;
  __afl_cmp_map->headers[k].hits = hits + 1;

  __afl_cmp_map->headers[k].shape = 7;

  hits &= CMP_MAP_H - 1;
  __afl_cmp_map->log[k][hits].v0 = arg1;
  __afl_cmp_map->log[k][hits].v1 = arg2;

}

#if defined(__APPLE__)
#pragma weak __sanitizer_cov_trace_const_cmp1 = __cmplog_ins_hook1
#pragma weak __sanitizer_cov_trace_const_cmp2 = __cmplog_ins_hook2
#pragma weak __sanitizer_cov_trace_const_cmp4 = __cmplog_ins_hook4
#pragma weak __sanitizer_cov_trace_const_cmp8 = __cmplog_ins_hook8

#pragma weak __sanitizer_cov_trace_cmp1 = __cmplog_ins_hook1
#pragma weak __sanitizer_cov_trace_cmp2 = __cmplog_ins_hook2
#pragma weak __sanitizer_cov_trace_cmp4 = __cmplog_ins_hook4
#pragma weak __sanitizer_cov_trace_cmp8 = __cmplog_ins_hook8
#else
void __sanitizer_cov_trace_const_cmp1(uint8_t arg1, uint8_t arg2)
    __attribute__((alias("__cmplog_ins_hook1")));
void __sanitizer_cov_trace_const_cmp2(uint16_t arg1, uint16_t arg2)
    __attribute__((alias("__cmplog_ins_hook2")));
void __sanitizer_cov_trace_const_cmp4(uint32_t arg1, uint32_t arg2)
    __attribute__((alias("__cmplog_ins_hook4")));
void __sanitizer_cov_trace_const_cmp8(uint64_t arg1, uint64_t arg2)
    __attribute__((alias("__cmplog_ins_hook8")));

void __sanitizer_cov_trace_cmp1(uint8_t arg1, uint8_t arg2)
    __attribute__((alias("__cmplog_ins_hook1")));
void __sanitizer_cov_trace_cmp2(uint16_t arg1, uint16_t arg2)
    __attribute__((alias("__cmplog_ins_hook2")));
void __sanitizer_cov_trace_cmp4(uint32_t arg1, uint32_t arg2)
    __attribute__((alias("__cmplog_ins_hook4")));
void __sanitizer_cov_trace_cmp8(uint64_t arg1, uint64_t arg2)
    __attribute__((alias("__cmplog_ins_hook8")));
#endif                                                /* defined(__APPLE__) */

void __sanitizer_cov_trace_switch(uint64_t val, uint64_t *cases) {

  for (uint64_t i = 0; i < cases[0]; i++) {

    uintptr_t k = (uintptr_t)__builtin_return_address(0) + i;
    k = (k >> 4) ^ (k << 8);
    k &= CMP_MAP_W - 1;

    __afl_cmp_map->headers[k].type = CMP_TYPE_INS;

    u32 hits = __afl_cmp_map->headers[k].hits;
    __afl_cmp_map->headers[k].hits = hits + 1;

    __afl_cmp_map->headers[k].shape = 7;

    hits &= CMP_MAP_H - 1;
    __afl_cmp_map->log[k][hits].v0 = val;
    __afl_cmp_map->log[k][hits].v1 = cases[i + 2];

  }

}

// POSIX shenanigan to see if an area is mapped.
// If it is mapped as X-only, we have a problem, so maybe we should add a check
// to avoid to call it on .text addresses
static int area_is_mapped(void *ptr, size_t len) {

  char *p = ptr;
  char *page = (char *)((uintptr_t)p & ~(sysconf(_SC_PAGE_SIZE) - 1));

  int r = msync(page, (p - page) + len, MS_ASYNC);
  if (r < 0) return errno != ENOMEM;
  return 1;

}

void __cmplog_rtn_hook(void *ptr1, void *ptr2) {

  if (!__afl_cmp_map) return;

  if (!area_is_mapped(ptr1, 32) || !area_is_mapped(ptr2, 32)) return;

  uintptr_t k = (uintptr_t)__builtin_return_address(0);
  k = (k >> 4) ^ (k << 8);
  k &= CMP_MAP_W - 1;

  __afl_cmp_map->headers[k].type = CMP_TYPE_RTN;

  u32 hits = __afl_cmp_map->headers[k].hits;
  __afl_cmp_map->headers[k].hits = hits + 1;

  __afl_cmp_map->headers[k].shape = 31;

  hits &= CMP_MAP_RTN_H - 1;
  __builtin_memcpy(((struct cmpfn_operands *)__afl_cmp_map->log[k])[hits].v0,
                   ptr1, 32);
  __builtin_memcpy(((struct cmpfn_operands *)__afl_cmp_map->log[k])[hits].v1,
                   ptr2, 32);

}

