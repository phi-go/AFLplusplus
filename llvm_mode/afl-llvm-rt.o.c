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


#include <zmq.h>
#include <sys/time.h>
#include <time.h>

#include <sys/mman.h>
#include <sys/shm.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <sys/mman.h>

#include <ucontext.h>

/* This is a somewhat ugly hack for the experimental 'trace-pc-guard' mode.
   Basically, we need to make sure that the forkserver is initialized after
   the LLVM-generated runtime initialization pass, not before. */

#ifdef USE_TRACE_PC
#define CONST_PRIO 5
#else
#define CONST_PRIO 0
#endif                                                     /* ^USE_TRACE_PC */

#include <sys/mman.h>
#include <fcntl.h>

/* Globals needed by the injected instrumentation. The __afl_area_initial region
   is used for instrumentation output before __afl_map_shm() has a chance to
   run. It will end up as .comm, so it shouldn't be too wasteful. */

u8  __afl_area_initial[MAP_SIZE];
u8 *__afl_area_ptr = __afl_area_initial;

#ifdef __ANDROID__
PREV_LOC_T __afl_prev_loc[MAX_NGRAM_SIZE];
u32        __afl_final_loc;
#else
__thread PREV_LOC_T __afl_prev_loc[MAX_NGRAM_SIZE];
__thread u32        __afl_final_loc;
#endif

struct cmp_map *__afl_cmp_map;
__thread u32    __afl_cmp_counter;

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

    /* create the shared memory segment as if it was a file */
    shm_fd = shm_open(shm_file_path, O_RDWR, 0600);
    if (shm_fd == -1) {

      fprintf(stderr, "shm_open() failed\n");
      exit(1);

    }

    /* map the shared memory segment to the address space of the process */
    shm_base = mmap(0, MAP_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED, shm_fd, 0);
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


static void * context = NULL;
static void * socket = NULL;

static void __connect_zmq(void) {
  const char * afl_zmq_url = getenv("IJON_ZMQ_FUZZER_URL");
  if (!afl_zmq_url) {
    return;
  }
  assert(context == NULL && socket == NULL);
  char zmq_id [128];
  char time_str[26];
  struct tm* tm_info;
  struct timeval tv;
  gettimeofday(&tv, NULL);
  tm_info = localtime(&tv.tv_sec);
  strftime(time_str, 26, "%Y:%m:%d-%H:%M:%S", tm_info);
  snprintf(zmq_id, 128, "P_%d_%s", getpid(), time_str);
  context = zmq_ctx_new();
  socket = zmq_socket(context, ZMQ_DEALER);
  zmq_setsockopt(socket, ZMQ_IDENTITY, zmq_id, strlen(zmq_id));

  if (zmq_connect(socket, afl_zmq_url) != 0) {
    fprintf(stderr, "ZMQ error: %s\n", zmq_strerror(errno));
    context = NULL;
    socket = NULL;
    return;
  } else {
    const char * msg = "P_UP";
    zmq_send(socket, msg, strlen(msg), 0);
  }
}


static int64_t __zmq_has_more() {
  int64_t more = 0;
  size_t more_size = sizeof(more);
  if (zmq_getsockopt(socket, ZMQ_RCVMORE, &more, &more_size) != 0) {
    fprintf(stderr, "ZMQ getsockopt: %s\n", zmq_strerror(errno));
  }
  return more;
}


static void __zmq_bb_req() {
  if (!__zmq_has_more()) {
    fprintf(stderr, "ZMQ expected more message parts for bb req but there are none\n");
    return;
  }

  void * pos;
  unsigned int size;
  if (zmq_recv(socket, &pos, sizeof(pos), 0) == -1) {
    fprintf(stderr, "ZMQ recv: %s\n", zmq_strerror(errno));
  }
  if (!__zmq_has_more()) {
    fprintf(stderr, "ZMQ expected more message parts for bb req but there are none\n");
    return;
  }
  if (zmq_recv(socket, &size, sizeof(size), 0) == -1) {
    fprintf(stderr, "ZMQ recv: %s\n", zmq_strerror(errno));
  }
  // send reply
  if (zmq_send(socket, "P_BB", 4, ZMQ_SNDMORE) == -1) {
    fprintf(stderr, "ZMQ send: %s\n", zmq_strerror(errno));
  }
  if (zmq_send(socket, &pos, sizeof(pos), ZMQ_SNDMORE) == -1) {
    fprintf(stderr, "ZMQ send: %s\n", zmq_strerror(errno));
  }
  if (zmq_send(socket, &size, sizeof(size), ZMQ_SNDMORE) == -1) {
    fprintf(stderr, "ZMQ send: %s\n", zmq_strerror(errno));
  }
  if (zmq_send(socket, pos, size, 0) == -1) {
    fprintf(stderr, "ZMQ send: %s\n", zmq_strerror(errno));
  }
}

/* ZMQ fork */
static void __afl_start_zmqserver(void) {
  s32 child_pid = fork();
  if (child_pid < 0) _exit(1);

  if (!child_pid) { // in child
    signal(SIGCHLD, SIG_DFL);
    __connect_zmq();
    char msg_type [5] = {0};
    while (socket) {
        if (zmq_recv(socket, msg_type, 4, 0) == -1) {
          fprintf(stderr, "ZMQ recv: %s\n", zmq_strerror(errno));
        }
        if (strncmp("BB_R", msg_type, 4) == 0) {
          __zmq_bb_req();
        } else if (strncmp("PDIE", msg_type, 4) == 0) {
          break;
        } else {
          fprintf(stderr, "ZMQ unknown message type: %s\n", msg_type);
        }
    }
    zmq_send(socket, "P_DE", 4, 0);
    zmq_close(socket);
    zmq_ctx_destroy(context);
    socket = NULL;
    context = NULL;
  }
  return;
}

void sigtrap_handler(int signo, siginfo_t *si, void* arg)
{
  assert(signo == SIGTRAP);
  ucontext_t *ctx = (ucontext_t *)arg;
  printf("RIP is %llx\n", ctx->uc_mcontext.gregs[REG_RIP]);
  uint8_t* rip = ctx->uc_mcontext.gregs[REG_RIP]-1;
  uint8_t* base = rip - ((uint64_t)rip)%4096;
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_WRITE|PROT_EXEC )==0);
  *rip=0x90; // replace int 3 by nop so we only have the interrupt once
  assert(mprotect((void*)base, 4096 , PROT_READ|PROT_EXEC )==0);
  ctx->uc_mcontext.gregs[REG_RIP] = rip;
}



/* Fork server logic. */

static void __afl_start_forkserver(void) {
  static u8 tmp[4];
  s32       child_pid;

  u8 child_stopped = 0;

  void (*old_sigchld_handler)(int) = 0;  // = signal(SIGCHLD, SIG_DFL);

  /* Phone home and tell the parent that we're OK. If parent isn't there,
     assume we're not running in forkserver mode and just execute program. */

  if (write(FORKSRV_FD + 1, tmp, 4) != 4) return;
  __afl_start_zmqserver();
  struct sigaction action;
  action.sa_sigaction = &sigtrap_handler;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGTRAP, &action, NULL);

  while (1) {

    u32 was_killed;
    int status;

    /* Wait for parent by reading from the pipe. Abort if read fails. */

    if (read(FORKSRV_FD, &was_killed, 4) != 4) _exit(1);

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

        if (socket) zmq_close(socket);
        if (context) zmq_ctx_destroy(context);

        close(FORKSRV_FD);
        close(FORKSRV_FD + 1);
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

  static u8  first_pass = 1;
  static u32 cycle_cnt;

  if (first_pass) {

    /* Make sure that every iteration of __AFL_LOOP() starts with a clean slate.
       On subsequent calls, the parent will take care of that, but on the first
       iteration, it's our job to erase any trace of whatever happened
       before the loop. */

    if (is_persistent) {

      memset(__afl_area_ptr, 0, MAP_SIZE);
      __afl_area_ptr[0] = 1;
      memset(__afl_prev_loc, 0, MAX_NGRAM_SIZE * sizeof(PREV_LOC_T));

    }

    cycle_cnt = max_cnt;
    first_pass = 0;
    return 1;

  }

  if (is_persistent) {

    if (--cycle_cnt) {

      raise(SIGSTOP);

      __afl_area_ptr[0] = 1;
      memset(__afl_prev_loc, 0, MAX_NGRAM_SIZE * sizeof(PREV_LOC_T));

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

void __cmplog_ins_hook1(uint8_t Arg1, uint8_t Arg2) {

  return;

}

void __cmplog_ins_hook2(uint16_t Arg1, uint16_t Arg2) {

  if (!__afl_cmp_map) return;

  uintptr_t k = (uintptr_t)__builtin_return_address(0);
  k = (k >> 4) ^ (k << 8);
  k &= CMP_MAP_W - 1;

  __afl_cmp_map->headers[k].type = CMP_TYPE_INS;

  u32 hits = __afl_cmp_map->headers[k].hits;
  __afl_cmp_map->headers[k].hits = hits + 1;
  // if (!__afl_cmp_map->headers[k].cnt)
  //  __afl_cmp_map->headers[k].cnt = __afl_cmp_counter++;

  __afl_cmp_map->headers[k].shape = 1;
  //__afl_cmp_map->headers[k].type = CMP_TYPE_INS;

  hits &= CMP_MAP_H - 1;
  __afl_cmp_map->log[k][hits].v0 = Arg1;
  __afl_cmp_map->log[k][hits].v1 = Arg2;

}

void __cmplog_ins_hook4(uint32_t Arg1, uint32_t Arg2) {

  if (!__afl_cmp_map) return;

  uintptr_t k = (uintptr_t)__builtin_return_address(0);
  k = (k >> 4) ^ (k << 8);
  k &= CMP_MAP_W - 1;

  __afl_cmp_map->headers[k].type = CMP_TYPE_INS;

  u32 hits = __afl_cmp_map->headers[k].hits;
  __afl_cmp_map->headers[k].hits = hits + 1;

  __afl_cmp_map->headers[k].shape = 3;

  hits &= CMP_MAP_H - 1;
  __afl_cmp_map->log[k][hits].v0 = Arg1;
  __afl_cmp_map->log[k][hits].v1 = Arg2;

}

void __cmplog_ins_hook8(uint64_t Arg1, uint64_t Arg2) {

  if (!__afl_cmp_map) return;

  uintptr_t k = (uintptr_t)__builtin_return_address(0);
  k = (k >> 4) ^ (k << 8);
  k &= CMP_MAP_W - 1;

  __afl_cmp_map->headers[k].type = CMP_TYPE_INS;

  u32 hits = __afl_cmp_map->headers[k].hits;
  __afl_cmp_map->headers[k].hits = hits + 1;

  __afl_cmp_map->headers[k].shape = 7;

  hits &= CMP_MAP_H - 1;
  __afl_cmp_map->log[k][hits].v0 = Arg1;
  __afl_cmp_map->log[k][hits].v1 = Arg2;

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
void __sanitizer_cov_trace_const_cmp1(uint8_t Arg1, uint8_t Arg2)
    __attribute__((alias("__cmplog_ins_hook1")));
void __sanitizer_cov_trace_const_cmp2(uint16_t Arg1, uint16_t Arg2)
    __attribute__((alias("__cmplog_ins_hook2")));
void __sanitizer_cov_trace_const_cmp4(uint32_t Arg1, uint32_t Arg2)
    __attribute__((alias("__cmplog_ins_hook4")));
void __sanitizer_cov_trace_const_cmp8(uint64_t Arg1, uint64_t Arg2)
    __attribute__((alias("__cmplog_ins_hook8")));

void __sanitizer_cov_trace_cmp1(uint8_t Arg1, uint8_t Arg2)
    __attribute__((alias("__cmplog_ins_hook1")));
void __sanitizer_cov_trace_cmp2(uint16_t Arg1, uint16_t Arg2)
    __attribute__((alias("__cmplog_ins_hook2")));
void __sanitizer_cov_trace_cmp4(uint32_t Arg1, uint32_t Arg2)
    __attribute__((alias("__cmplog_ins_hook4")));
void __sanitizer_cov_trace_cmp8(uint64_t Arg1, uint64_t Arg2)
    __attribute__((alias("__cmplog_ins_hook8")));
#endif                                                /* defined(__APPLE__) */

void __sanitizer_cov_trace_switch(uint64_t Val, uint64_t *Cases) {

  for (uint64_t i = 0; i < Cases[0]; i++) {

    uintptr_t k = (uintptr_t)__builtin_return_address(0) + i;
    k = (k >> 4) ^ (k << 8);
    k &= CMP_MAP_W - 1;

    __afl_cmp_map->headers[k].type = CMP_TYPE_INS;

    u32 hits = __afl_cmp_map->headers[k].hits;
    __afl_cmp_map->headers[k].hits = hits + 1;

    __afl_cmp_map->headers[k].shape = 7;

    hits &= CMP_MAP_H - 1;
    __afl_cmp_map->log[k][hits].v0 = Val;
    __afl_cmp_map->log[k][hits].v1 = Cases[i + 2];

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

