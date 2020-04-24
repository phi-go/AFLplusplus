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

#ifdef __linux__
#include "snapshot-inl.h"
#endif

/* This is a somewhat ugly hack for the experimental 'trace-pc-guard' mode.
   Basically, we need to make sure that the forkserver is initialized after
   the LLVM-generated runtime initialization pass, not before. */

#define CONST_PRIO 5

#include <sys/mman.h>
#include <fcntl.h>

/* Globals needed by the injected instrumentation. The __afl_area_initial region
   is used for instrumentation output before __afl_map_shm() has a chance to
   run. It will end up as .comm, so it shouldn't be too wasteful. */

u8  __afl_area_initial[MAP_SIZE];
u8 *__afl_area_ptr = __afl_area_initial;
u8 *__afl_dictionary;

#ifdef __ANDROID__
PREV_LOC_T __afl_prev_loc[NGRAM_SIZE_MAX];
u32        __afl_final_loc;
u32        __afl_prev_ctx;
u32        __afl_cmp_counter;
u32        __afl_dictionary_len;
#else
__thread PREV_LOC_T __afl_prev_loc[NGRAM_SIZE_MAX];
__thread u32        __afl_final_loc;
__thread u32        __afl_prev_ctx;
__thread u32        __afl_cmp_counter;
__thread u32        __afl_dictionary_len;
#endif

struct cmp_map *__afl_cmp_map;

/* Running in persistent mode? */

static u8 is_persistent;

/* SHM setup. */

static void __afl_map_shm(void) {

  u8 *id_str = getenv(SHM_ENV_VAR);

  /* If we're running under AFL, attach to the appropriate region, replacing the
     early-stage __afl_area_initial region that is needed to allow some really
     hacky .init code to work correctly in projects such as OpenSSL. */

  if (id_str) {

#ifdef USEMMAP
    const char *   shm_file_path = id_str;
    int            shm_fd = -1;
    unsigned char *shm_base = NULL;
    unsigned int   map_size = MAP_SIZE

        if (__afl_final_loc > 1 && __afl_final_loc < MAP_SIZE) map_size =
            __afl_final_loc;

    /* create the shared memory segment as if it was a file */
    shm_fd = shm_open(shm_file_path, O_RDWR, 0600);
    if (shm_fd == -1) {

      fprintf(stderr, "shm_open() failed\n");
      exit(1);

    }

    /* map the shared memory segment to the address space of the process */
    shm_base = mmap(0, map_size, PROT_READ | PROT_WRITE, MAP_SHARED, shm_fd, 0);
    if (shm_base == MAP_FAILED) {

      close(shm_fd);
      shm_fd = -1;

      fprintf(stderr, "mmap() failed\n");
      exit(2);

    }

    __afl_area_ptr = shm_base;
#else
    u32 shm_id = atoi(id_str);

    __afl_area_ptr = shmat(shm_id, NULL, 0);
#endif

    /* Whooooops. */

    if (__afl_area_ptr == (void *)-1) _exit(1);

    /* Write something into the bitmap so that even with low AFL_INST_RATIO,
       our parent doesn't give up on us. */

    __afl_area_ptr[0] = 1;

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
  u32       map_size = MAP_SIZE;
  u32       already_read_first = 0;
  u32       was_killed;

  if (__afl_final_loc > 1 && __afl_final_loc < MAP_SIZE)
    map_size = __afl_final_loc;

  u8 child_stopped = 0;

  void (*old_sigchld_handler)(int) = 0;  // = signal(SIGCHLD, SIG_DFL);

  /* Phone home and tell the parent that we're OK. If parent isn't there,
     assume we're not running in forkserver mode and just execute program. */

  status |= (FS_OPT_ENABLED | FS_OPT_SNAPSHOT);
  if (map_size <= 0x800000)
    status |= (FS_OPT_SET_MAPSIZE(map_size) | FS_OPT_MAPSIZE);
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

#define read_from_command_pipe(V) \
    if ((read(FORKSRV_FD + 2, &V, sizeof(V)) != sizeof(V))) { \
      fprintf(stderr, "command read failed %s:%d\n", __FILE__, __LINE__); \
      _exit(1); \
    }

#define READ_FROM_COMMAND_PIPE2(V, S) \
    if ((read(FORKSRV_FD + 2, V, S) != S)) { \
      fprintf(stderr, "command read failed %s:%d\n", __FILE__, __LINE__); \
      _exit(1); \
    }

#define write_to_command_pipe(V, S) \
    if ((write(FORKSRV_FD + 3, V, S) != S)) { \
      fprintf(stderr, "command write failed %s:%d\n", __FILE__, __LINE__); \
      _exit(1); \
    }

#define NULL_CHECK(P) \
  if (P == NULL) { \
      fprintf(stderr, "ptr should not be null %s:%d\n", __FILE__, __LINE__); \
      _exit(1); \
  }

struct BBReq {
  void * pos;
  int size;
};

typedef enum {NO_MORE=-1, CMP=1} annotation_action_t;

#define MAX_INSTRUCTION_SIZE 16

typedef struct action {
  annotation_action_t action;
  uint8_t * pos;
  uint8_t instruction_size;
  char instruction_bytes[MAX_INSTRUCTION_SIZE];
  void * bb_annotation_id;
  struct action * bb_next;
  struct action * pos_next;
} action_t;

typedef struct bb_annotation {
  void * pos;
  int shm_id;
  void * shm_addr;
  action_t * actions;
  UT_hash_handle hh;
} bb_annotation_t;

typedef struct pos_actions {
  void * pos;
  action_t * actions;
  UT_hash_handle hh;
} pos_actions_t;

bb_annotation_t * bb_annotations_map = NULL;
pos_actions_t * pos_actions_map = NULL;

__thread unsigned int single_step_size = 0;

void set_breakpoint(action_t * action, int quiet) {
  if (!(*action->pos == 0xCC || *action->pos == (uint8_t)action->instruction_bytes[0])) {
      fprintf(stderr, "ann req pos (%p) is not 0xCC or expected initial 0x%x but 0x%x\n",
      action->pos, (uint8_t)action->instruction_bytes[0], *action->pos);
      _exit(1);
  }
  if (!quiet) {
    fprintf(stderr, "setting breakpoint at %p\n", action->pos);
  }

  uint8_t* base = action->pos - ((uint64_t)action->pos)%4096;
  // TODO find initial protections to restore them
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_WRITE|PROT_EXEC )==0);
  *(uint8_t*)action->pos = 0xcc;
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_EXEC )==0);
}

void remove_breakpoint(action_t * action, int quiet) {
  if (*action->pos != 0xcc) {
      fprintf(stderr, "deann req pos (%lx) is not 0xcc but 0x%x\n", action->pos, *action->pos);
      _exit(1);
  }
  if (!quiet) {
    fprintf(stderr, "removing breakpoint at %p\n", action->pos);
  }

  uint8_t* base = action->pos - ((uint64_t)action->pos)%4096;
  // TODO find initial protections to restore them
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_WRITE|PROT_EXEC )==0);
  *(uint8_t*)action->pos = (uint8_t)action->instruction_bytes[0];
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_EXEC )==0);
}

#define CHECK_BIT(var,pos) (!!((var) & (pos)))

void sigtrap_handler(int signo, siginfo_t *si, void* arg)
{
  assert(signo == SIGTRAP);
  ucontext_t *ctx = (ucontext_t *)arg;
  if (single_step_size == 0) {
    // we only expect to land here if we set a bp, a bp (0xcc / int 3) is one byte long
    // and instructions are completed before we get to the signal handler
    // so subtract one from our position
    const uint8_t * pos = (uint8_t *)ctx->uc_mcontext.gregs[REG_RIP] - 1;

    pos_actions_t * actions;
    HASH_FIND_PTR(pos_actions_map, &pos, actions);
    if (actions) {
      action_t * act = actions->actions;

      // restore old instruction and single step once then we can get the result
      single_step_size = act->instruction_size;
      
      // set trap flag to start tracing
      ctx->uc_mcontext.gregs[REG_EFL] |= 0x100;

      // set RIP so that instruction is repeated
      ctx->uc_mcontext.gregs[REG_RIP] -= 1;

      remove_breakpoint(act, /*quiet*/ 1);
    } else {
      fprintf(stderr, "no actions for %p found (before stepping)\n", pos);
    }
    return;
  } else {
    const uint8_t * pos = (uint8_t *)ctx->uc_mcontext.gregs[REG_RIP] - single_step_size;
    pos_actions_t * actions;
    HASH_FIND_PTR(pos_actions_map, &pos, actions);
    if (actions) {
      action_t * act = actions->actions;
      set_breakpoint(act, /*quiet*/ 1);
      LL_FOREACH2(actions->actions, act, pos_next) {
        if (act->action == CMP) {
          // int CF = CHECK_BIT(ctx->uc_mcontext.gregs[REG_EFL], 0x0001);
          // int OF = CHECK_BIT(ctx->uc_mcontext.gregs[REG_EFL], 0x0800);
          // int SF = CHECK_BIT(ctx->uc_mcontext.gregs[REG_EFL], 0x0080);
          // int ZF = CHECK_BIT(ctx->uc_mcontext.gregs[REG_EFL], 0x0040);
          // int AF = CHECK_BIT(ctx->uc_mcontext.gregs[REG_EFL], 0x0010);
          // int PF = CHECK_BIT(ctx->uc_mcontext.gregs[REG_EFL], 0x0004);

          // fprintf(stderr, "(%p) CF:%d OF:%d SF:%d ZF:%d AF:%d PF:%d\n", act->pos, CF, OF, SF, ZF, AF, PF);
        }
      }
    } else {
      fprintf(stderr, "no actions for %p found (after stepping %d - real pos %p)\n",
              pos, single_step_size, (uint8_t *)ctx->uc_mcontext.gregs[REG_RIP]);
    }

    // unset trap flag
    ctx->uc_mcontext.gregs[REG_EFL] &= ~0x100;

    single_step_size = 0;
  }
}

static void __afl_handle_bb_req(void) {
    struct BBReq req;
    read_from_command_pipe(req);
    write_to_command_pipe(req.pos, req.size);
}

void remove_bb_annotation(void * bb_annotation_id) {
  // find bb annotation
  bb_annotation_t * annotation;
  HASH_FIND_PTR(bb_annotations_map, &bb_annotation_id, annotation);
  if (annotation == NULL) {
      fprintf(stderr, "expected annotation for %p to exist\n", bb_annotation_id);
      _exit(1);
  }

  // for all actions belonging to bb annotation find them and remove them
  action_t * el = NULL;
  action_t * tmp = NULL;
  LL_FOREACH_SAFE2(annotation->actions, el, tmp, bb_next) {
    LL_DELETE2(annotation->actions, el, bb_next);
    pos_actions_t * pos_action;
    HASH_FIND_PTR(pos_actions_map, &el->pos, pos_action);
    if (!pos_action) {
      fprintf(stderr, "expected pos_action for %p to exist\n", el->pos);
    }
    LL_DELETE2(pos_action->actions, el, pos_next);
    action_t * count_el = NULL;
    int count = -1;
    LL_COUNT2(pos_action->actions, count_el, count, pos_next);
    if (count == 0) {
      HASH_DEL(pos_actions_map, pos_action);
      free(pos_action);

      // remove breakpoint
      remove_breakpoint(el, /*quiet*/ 0);
    }

    free(el);
  }

  // free bb annotation
  shmdt(annotation->shm_addr);
  annotation->shm_addr = NULL;
  HASH_DEL(bb_annotations_map, annotation);
  free(annotation);

  fprintf(stderr, "there are %d annotations, %d actions\n",
          HASH_COUNT(bb_annotations_map), HASH_COUNT(pos_actions_map));
}

static void __afl_handle_ann_req(void) {
  // get bb_annotation
  bb_annotation_t * bb_ann = calloc(1, sizeof(*bb_ann));
  NULL_CHECK(bb_ann);
  bb_ann->actions = NULL;
  read_from_command_pipe(bb_ann->pos);
  read_from_command_pipe(bb_ann->shm_id);
  bb_ann->shm_addr = shmat(bb_ann->shm_id, NULL, 0);
  if (bb_ann->shm_addr == (void *) -1) {
    perror("could not get shm segment");
    _exit(1);
  }
  HASH_ADD_PTR(bb_annotations_map, pos, bb_ann);

  // get all actions for that bb_annotation
  while (1) {
    annotation_action_t action_type;
    read_from_command_pipe(action_type);
    if (action_type == NO_MORE) {
      break;
    }

    action_t * action = calloc(1, sizeof(*action));
    NULL_CHECK(action);
    action->action = action_type;
    read_from_command_pipe(action->pos);
    read_from_command_pipe(action->instruction_size);
    READ_FROM_COMMAND_PIPE2(&action->instruction_bytes, action->instruction_size);
    action->bb_annotation_id = bb_ann->pos;
    action->bb_next = NULL;
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
    LL_PREPEND2(bb_ann->actions, action, bb_next);

    // set breakpoint to enable action
    set_breakpoint(action, /*quiet*/ 0);
  }

  fprintf(stderr, "there are %d annotations, %d actions\n",
          HASH_COUNT(bb_annotations_map), HASH_COUNT(pos_actions_map));
}

static void __afl_handle_deann_req(void) {
  void * pos = 0;
  read_from_command_pipe(pos);
  remove_bb_annotation(pos);
  // TODO return command success?
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
  u32 map_size = MAP_SIZE;
  u32 already_read_first = 0;
  u32 was_killed;

  if (__afl_final_loc > 1 && __afl_final_loc < MAP_SIZE)
    map_size = __afl_final_loc;

  u8 child_stopped = 0;

  void (*old_sigchld_handler)(int) = 0;  // = signal(SIGCHLD, SIG_DFL);

  if (map_size <= 0x800000)
    status |= (FS_OPT_SET_MAPSIZE(map_size) | FS_OPT_MAPSIZE);
  if (__afl_dictionary_len > 0 && __afl_dictionary) status |= FS_OPT_AUTODICT;
  if (status) status |= (FS_OPT_ENABLED);
  memcpy(tmp, &status, 4);

  /* Phone home and tell the parent that we're OK. If parent isn't there,
     assume we're not running in forkserver mode and just execute program. */

  if (write(FORKSRV_FD + 1, tmp, 4) != 4) return;
  struct sigaction action;
  action.sa_sigaction = &sigtrap_handler;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGTRAP, &action, NULL);

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
      char cmd[4] = {0};
      read_from_command_pipe(cmd);
      // if ((read(FORKSRV_FD + 2, &cmd, 4) != 4)) {
      //   fprintf(stderr, "command read failed %s\n", cmd);
      //   _exit(1);
      // }
      if (strncmp("BB_R", cmd, 4) == 0) {
        __afl_handle_bb_req();
      } else if (strncmp("EANR", cmd, 4) == 0) {
        __afl_handle_ann_req();
      } else if (strncmp("DANR", cmd, 4) == 0) {
        __afl_handle_deann_req();
      } else {
        fprintf(stderr, "fuzzee unknown command: %s\n", cmd);
      }
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

      /* Once woken up, create a clone of our process. */

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

    /* Relay wait status to pipe, then loop back. */

    if (write(FORKSRV_FD + 1, &status, 4) != 4) _exit(1);

  }

}

/* A simplified persistent mode handler, used as explained in
 * llvm_mode/README.md. */

int __afl_persistent_loop(unsigned int max_cnt) {

  static u8    first_pass = 1;
  static u32   cycle_cnt;
  unsigned int map_size = MAP_SIZE;

  if (__afl_final_loc > 1 && __afl_final_loc < MAP_SIZE)
    map_size = __afl_final_loc;

  if (first_pass) {

    /* Make sure that every iteration of __AFL_LOOP() starts with a clean slate.
       On subsequent calls, the parent will take care of that, but on the first
       iteration, it's our job to erase any trace of whatever happened
       before the loop. */

    if (is_persistent) {

      memset(__afl_area_ptr, 0, map_size);
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

