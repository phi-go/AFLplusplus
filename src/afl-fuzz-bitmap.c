/*
   american fuzzy lop++ - bitmap related routines
   ----------------------------------------------

   Originally written by Michal Zalewski

   Now maintained by Marc Heuse <mh@mh-sec.de>,
                        Heiko Eißfeldt <heiko.eissfeldt@hexco.de> and
                        Andrea Fioraldi <andreafioraldi@gmail.com>

   Copyright 2016, 2017 Google Inc. All rights reserved.
   Copyright 2019-2020 AFLplusplus Project. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This is the real deal: the program takes an instrumented binary and
   attempts a variety of basic fuzzing tricks, paying close attention to
   how they affect the execution path.

 */

#include "afl-fuzz.h"
#include <limits.h>

/* Write bitmap to file. The bitmap is useful mostly for the secret
   -B option, to focus a separate fuzzing session on a particular
   interesting input without rediscovering all the others. */

void write_bitmap(afl_state_t *afl) {

  u8  fname[PATH_MAX];
  s32 fd;

  if (!afl->bitmap_changed) { return; }
  afl->bitmap_changed = 0;

  snprintf(fname, PATH_MAX, "%s/fuzz_bitmap", afl->out_dir);
  fd = open(fname, O_WRONLY | O_CREAT | O_TRUNC, 0600);

  if (fd < 0) { PFATAL("Unable to open '%s'", fname); }

  ck_write(fd, afl->virgin_bits, afl->fsrv.map_size, fname);

  close(fd);

}

/* Check if the current execution path brings anything new to the table.
   Update virgin bits to reflect the finds. Returns 1 if the only change is
   the hit-count for a particular tuple; 2 if there are new tuples seen.
   Updates the map, so subsequent calls will always return 0.

   This function is called after every exec() on a fairly large buffer, so
   it needs to be fast. We do this in 32-bit and 64-bit flavors. */

u8 has_new_bits(afl_state_t *afl, u8 *virgin_map) {

#ifdef WORD_SIZE_64

  u64 *current = (u64 *)afl->fsrv.trace_bits;
  u64 *virgin = (u64 *)virgin_map;

  u32 i = (afl->fsrv.map_size >> 3);

#else

  u32 *current = (u32 *)afl->fsrv.trace_bits;
  u32 *virgin = (u32 *)virgin_map;

  u32 i = (afl->fsrv.map_size >> 2);

#endif                                                     /* ^WORD_SIZE_64 */
  // the map size must be a minimum of 8 bytes.
  // for variable/dynamic map sizes this is ensured in the forkserver

  u8 ret = 0;

  while (i--) {

    /* Optimize for (*current & *virgin) == 0 - i.e., no bits in current bitmap
       that have not been already cleared from the virgin map - since this will
       almost always be the case. */

    // the (*current) is unnecessary but speeds up the overall comparison
    if (unlikely(*current) && unlikely(*current & *virgin)) {

      if (likely(ret < 2)) {

        u8 *cur = (u8 *)current;
        u8 *vir = (u8 *)virgin;

        /* Looks like we have not found any new bytes yet; see if any non-zero
           bytes in current[] are pristine in virgin[]. */

#ifdef WORD_SIZE_64

        if (*virgin == 0xffffffffffffffff || (cur[0] && vir[0] == 0xff) ||
            (cur[1] && vir[1] == 0xff) || (cur[2] && vir[2] == 0xff) ||
            (cur[3] && vir[3] == 0xff) || (cur[4] && vir[4] == 0xff) ||
            (cur[5] && vir[5] == 0xff) || (cur[6] && vir[6] == 0xff) ||
            (cur[7] && vir[7] == 0xff)) {

          ret = 2;

        } else {

          ret = 1;

        }

#else

        if (*virgin == 0xffffffff || (cur[0] && vir[0] == 0xff) ||
            (cur[1] && vir[1] == 0xff) || (cur[2] && vir[2] == 0xff) ||
            (cur[3] && vir[3] == 0xff))
          ret = 2;
        else
          ret = 1;

#endif                                                     /* ^WORD_SIZE_64 */

      }

      *virgin &= ~*current;

    }

    ++current;
    ++virgin;

  }

  if (unlikely(ret) && likely(virgin_map == afl->virgin_bits)) {

    afl->bitmap_changed = 1;

  }

  return ret;

}

/* Count the number of bits set in the provided bitmap. Used for the status
   screen several times every second, does not have to be fast. */

u32 count_bits(afl_state_t *afl, u8 *mem) {

  u32 *ptr = (u32 *)mem;
  u32  i = (afl->fsrv.map_size >> 2);
  u32  ret = 0;

  while (i--) {

    u32 v = *(ptr++);

    /* This gets called on the inverse, virgin bitmap; optimize for sparse
       data. */

    if (v == 0xffffffff) {

      ret += 32;
      continue;

    }

    v -= ((v >> 1) & 0x55555555);
    v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
    ret += (((v + (v >> 4)) & 0xF0F0F0F) * 0x01010101) >> 24;

  }

  return ret;

}

/* Count the number of bytes set in the bitmap. Called fairly sporadically,
   mostly to update the status screen or calibrate and examine confirmed
   new paths. */

u32 count_bytes(afl_state_t *afl, u8 *mem) {

  u32 *ptr = (u32 *)mem;
  u32  i = (afl->fsrv.map_size >> 2);
  u32  ret = 0;

  while (i--) {

    u32 v = *(ptr++);

    if (!v) { continue; }
    if (v & 0x000000ff) { ++ret; }
    if (v & 0x0000ff00) { ++ret; }
    if (v & 0x00ff0000) { ++ret; }
    if (v & 0xff000000) { ++ret; }

  }

  return ret;

}

/* Count the number of non-255 bytes set in the bitmap. Used strictly for the
   status screen, several calls per second or so. */

u32 count_non_255_bytes(afl_state_t *afl, u8 *mem) {

  u32 *ptr = (u32 *)mem;
  u32  i = (afl->fsrv.map_size >> 2);
  u32  ret = 0;

  while (i--) {

    u32 v = *(ptr++);

    /* This is called on the virgin bitmap, so optimize for the most likely
       case. */

    if (v == 0xffffffff) { continue; }
    if ((v & 0x000000ff) != 0x000000ff) { ++ret; }
    if ((v & 0x0000ff00) != 0x0000ff00) { ++ret; }
    if ((v & 0x00ff0000) != 0x00ff0000) { ++ret; }
    if ((v & 0xff000000) != 0xff000000) { ++ret; }

  }

  return ret;

}

/* Destructively simplify trace by eliminating hit count information
   and replacing it with 0x80 or 0x01 depending on whether the tuple
   is hit or not. Called on every new crash or timeout, should be
   reasonably fast. */

const u8 simplify_lookup[256] = {

    [0] = 1, [1 ... 255] = 128

};

#ifdef WORD_SIZE_64

void simplify_trace(afl_state_t *afl, u64 *mem) {

  u32 i = (afl->fsrv.map_size >> 3);

  while (i--) {

    /* Optimize for sparse bitmaps. */

    if (unlikely(*mem)) {

      u8 *mem8 = (u8 *)mem;

      mem8[0] = simplify_lookup[mem8[0]];
      mem8[1] = simplify_lookup[mem8[1]];
      mem8[2] = simplify_lookup[mem8[2]];
      mem8[3] = simplify_lookup[mem8[3]];
      mem8[4] = simplify_lookup[mem8[4]];
      mem8[5] = simplify_lookup[mem8[5]];
      mem8[6] = simplify_lookup[mem8[6]];
      mem8[7] = simplify_lookup[mem8[7]];

    } else {

      *mem = 0x0101010101010101ULL;

    }

    ++mem;

  }

}

#else

void simplify_trace(afl_state_t *afl, u32 *mem) {

  u32 i = (afl->fsrv.map_size >> 2);

  while (i--) {

    /* Optimize for sparse bitmaps. */

    if (unlikely(*mem)) {

      u8 *mem8 = (u8 *)mem;

      mem8[0] = simplify_lookup[mem8[0]];
      mem8[1] = simplify_lookup[mem8[1]];
      mem8[2] = simplify_lookup[mem8[2]];
      mem8[3] = simplify_lookup[mem8[3]];

    } else

      *mem = 0x01010101;

    ++mem;

  }

}

#endif                                                     /* ^WORD_SIZE_64 */

/* Destructively classify execution counts in a trace. This is used as a
   preprocessing step for any newly acquired traces. Called on every exec,
   must be fast. */

static const u8 count_class_lookup8[256] = {

    [0] = 0,
    [1] = 1,
    [2] = 2,
    [3] = 4,
    [4 ... 7] = 8,
    [8 ... 15] = 16,
    [16 ... 31] = 32,
    [32 ... 127] = 64,
    [128 ... 255] = 128

};

static u16 count_class_lookup16[65536];

void init_count_class16(void) {

  u32 b1, b2;

  for (b1 = 0; b1 < 256; b1++) {

    for (b2 = 0; b2 < 256; b2++) {

      count_class_lookup16[(b1 << 8) + b2] =
          (count_class_lookup8[b1] << 8) | count_class_lookup8[b2];

    }

  }

}

#ifdef WORD_SIZE_64

void classify_counts(afl_forkserver_t *fsrv) {

  u64 *mem = (u64 *)fsrv->trace_bits;

  u32 i = (fsrv->map_size >> 3);

  while (i--) {

    /* Optimize for sparse bitmaps. */

    if (unlikely(*mem)) {

      u16 *mem16 = (u16 *)mem;

      mem16[0] = count_class_lookup16[mem16[0]];
      mem16[1] = count_class_lookup16[mem16[1]];
      mem16[2] = count_class_lookup16[mem16[2]];
      mem16[3] = count_class_lookup16[mem16[3]];

    }

    ++mem;

  }

}

#else

void classify_counts(afl_forkserver_t *fsrv) {

  u32 *mem = (u32 *)fsrv->trace_bits;

  u32 i = (fsrv->map_size >> 2);

  while (i--) {

    /* Optimize for sparse bitmaps. */

    if (unlikely(*mem)) {

      u16 *mem16 = (u16 *)mem;

      mem16[0] = count_class_lookup16[mem16[0]];
      mem16[1] = count_class_lookup16[mem16[1]];

    }

    ++mem;

  }

}

#endif                                                     /* ^WORD_SIZE_64 */

/* Compact trace bytes into a smaller bitmap. We effectively just drop the
   count information here. This is called only sporadically, for some
   new paths. */

void minimize_bits(afl_state_t *afl, u8 *dst, u8 *src) {

  u32 i = 0;

  while (i < afl->fsrv.map_size) {

    if (*(src++)) { dst[i >> 3] |= 1 << (i & 7); }
    ++i;

  }

}

#ifndef SIMPLE_FILES

/* Construct a file name for a new test case, capturing the operation
   that led to its discovery. Returns a ptr to afl->describe_op_buf_256. */

u8 *describe_op(afl_state_t *afl, u8 hnb, int64_t hne) {

  u8 *ret = afl->describe_op_buf_256;

  if (unlikely(afl->syncing_annotation)) {

    sprintf(ret, "ann_sync_src:%06u,time:%llu",
            afl->queue_cur->id, get_cur_time() - afl->start_time);

  } else if (unlikely(afl->syncing_party)) {

    sprintf(ret, "sync:%s,src:%06u", afl->syncing_party, afl->syncing_case);

  } else {

    sprintf(ret, "src:%06u", afl->queue_cur->id);

    sprintf(ret + strlen(ret), ",time:%llu", get_cur_time() - afl->start_time);

    if (afl->splicing_with >= 0) {

      sprintf(ret + strlen(ret), "+%06d", afl->splicing_with);

    }

    sprintf(ret + strlen(ret), ",op:%s", afl->stage_short);

    if (afl->stage_cur_byte >= 0) {

      sprintf(ret + strlen(ret), ",pos:%d", afl->stage_cur_byte);

      if (afl->stage_val_type != STAGE_VAL_NONE) {

        sprintf(ret + strlen(ret), ",val:%s%+d",
                (afl->stage_val_type == STAGE_VAL_BE) ? "be:" : "",
                afl->stage_cur_val);

      }

    } else {

      sprintf(ret + strlen(ret), ",rep:%d", afl->stage_cur_val);

    }

  }

  if (hne > -1) {
    sprintf(ret + strlen(ret), ",edge:%06lu", hne);
  }
  if (hnb == 2) { strcat(ret, ",+cov"); }

  return ret;

}

#endif                                                     /* !SIMPLE_FILES */

/* Write a message accompanying the crash directory :-) */

static void write_crash_readme(afl_state_t *afl) {

  u8    fn[PATH_MAX];
  s32   fd;
  FILE *f;

  u8 val_buf[STRINGIFY_VAL_SIZE_MAX];

  sprintf(fn, "%s/crashes/README.txt", afl->out_dir);

  fd = open(fn, O_WRONLY | O_CREAT | O_EXCL, 0600);

  /* Do not die on errors here - that would be impolite. */

  if (unlikely(fd < 0)) { return; }

  f = fdopen(fd, "w");

  if (unlikely(!f)) {

    close(fd);
    return;

  }

  fprintf(
      f,
      "Command line used to find this crash:\n\n"

      "%s\n\n"

      "If you can't reproduce a bug outside of afl-fuzz, be sure to set the "
      "same\n"
      "memory limit. The limit used for this fuzzing session was %s.\n\n"

      "Need a tool to minimize test cases before investigating the crashes or "
      "sending\n"
      "them to a vendor? Check out the afl-tmin that comes with the fuzzer!\n\n"

      "Found any cool bugs in open-source tools using afl-fuzz? If yes, please "
      "drop\n"
      "an mail at <afl-users@googlegroups.com> once the issues are fixed\n\n"

      "  https://github.com/AFLplusplus/AFLplusplus\n\n",

      afl->orig_cmdline,
      stringify_mem_size(val_buf, sizeof(val_buf),
                         afl->fsrv.mem_limit << 20));      /* ignore errors */

  fclose(f);

}

static int knows_hash(annotation_t * ann, uint64_t contender) {
  if (get_head(&ann->meta_node_hashes)->next) {
    LIST_FOREACH(&ann->meta_node_hashes, uint64_t, {
      if (contender == *el) {
        return 1;
      }
    });
  }
  return 0;
}


/* Check if the result of an execve() during routine fuzzing is interesting,
   save or queue the input test case for further analysis if so. Returns 1 if
   entry is saved, 0 otherwise. */

u8 save_if_interesting(afl_state_t *afl, void *mem, u32 len, u8 fault) {

  if (unlikely(len == 0)) { return 0; }

  u8 *queue_fn = "";
  u8  hnb = '\0';
  s32 fd;
  u8  keeping = 0, res;

  u8 fn[PATH_MAX];

  u32 cksum = hash32(afl->fsrv.trace_bits, afl->fsrv.map_size, HASH_CONST);

  if (unlikely(fault == afl->crash_mode)) {

    int ia = 0;
    int64_t hne = -1; // has new edges
    // keep if annotations are improved
    if (get_head(&afl->active_annotations)->next) {
      LIST_FOREACH(&afl->active_annotations, annotation_t, {
        if (el->ignored) {
          continue;
        }
        int improvement = 0;
        int candidate = 0;
        u8 ann_best_for_pos[ANNOTATION_RESULT_SIZE] = { 0 };
        uint64_t num_writes = el->shm_addr->num_writes_during_run;
        if (num_writes) {
          switch(el->type) {
            case ANN_MIN_SINGLE:
            case ANN_MIN_ADDRESS:
              {
                if (num_writes > 0) {
                  uint64_t contender = el->shm_addr->result.best_values[0];
                  if (contender < el->cur_best.best_values[0]) {
                    if (el->cur_best.best_values[0] == UINT64_MAX) {
                      candidate = 1;
                    }
                    el->cur_best.best_values[0] = contender;
                    el->max_pos = 0;
                    improvement += 1;
                    ann_best_for_pos[0] = 1;
                    zmq_send_annotation_update(afl, el->id, 0, contender);
                  }
                }
              }
              break;
            case ANN_MAX_SINGLE:
            case ANN_MAX_ADDRESS:
              {
                if (num_writes > 0) {
                  uint64_t contender = el->shm_addr->result.best_values[0];
                  if (contender > el->cur_best.best_values[0]) {
                    if (el->cur_best.best_values[0] == 0) {
                      candidate = 1;
                    }
                    el->cur_best.best_values[0] = contender;
                    el->max_pos = 0;
                    improvement += 1;
                    ann_best_for_pos[0] = 1;
                    zmq_send_annotation_update(afl, el->id, 0, contender);
                  }
                }
              }
              break;
            case ANN_MIN_ITER:
              {
                for (int i = 0; i < num_writes; i++) {
                  uint64_t contender = el->shm_addr->result.best_values[i];
                  if (contender < el->cur_best.best_values[i]) {
                    if (el->cur_best.best_values[i] == UINT64_MAX) {
                      candidate = 1;
                    }
                    el->cur_best.best_values[i] = contender;
                    improvement += 1;
                    if (i > el->max_pos) { el->max_pos = i; }
                    ann_best_for_pos[i] = 1;
                    zmq_send_annotation_update(afl, el->id, i, contender);
                  }
                }
              }
              break;
            case ANN_MAX_ITER:
              {
                for (int i = 0; i < num_writes; i++) {
                  uint64_t contender = el->shm_addr->result.best_values[i];
                  if (contender > el->cur_best.best_values[i]) {
                    if (el->cur_best.best_values[i] == 0) {
                      candidate = 1;
                    }
                    el->cur_best.best_values[i] = contender;
                    improvement += 1;
                    if (i > el->max_pos) { el->max_pos = i; }
                    ann_best_for_pos[i] = 1;
                    zmq_send_annotation_update(afl, el->id, i, contender);
                  }
                }
              }
              break;
            case ANN_OVERFLOW:
              {
                {
                  uint64_t overflow = el->shm_addr->result.best_values[0];
                  if (overflow) {
                    zmq_send_annotation_update(afl, el->id, 0, 0);
                  }
                  uint64_t contender = el->shm_addr->result.best_values[1];
                  if (contender < el->cur_best.best_values[1]) {
                    if (el->cur_best.best_values[1] == UINT64_MAX) {
                      candidate = 1;
                    }
                    el->cur_best.best_values[1] = contender;
                    improvement += 1;
                    ann_best_for_pos[0] = 1;
                    zmq_send_annotation_update(afl, el->id, 0, contender+1);
                  }
                }

                {
                  uint64_t overflow = el->shm_addr->result.best_values[2];
                  if (overflow) {
                    zmq_send_annotation_update(afl, el->id, 1, 0);
                  }
                  uint64_t contender = el->shm_addr->result.best_values[3];
                  if (contender < el->cur_best.best_values[3]) {
                    if (el->cur_best.best_values[3] == UINT64_MAX) {
                      candidate = 1;
                    }
                    el->cur_best.best_values[3] = contender;
                    improvement += 1;
                    ann_best_for_pos[1] = 1;
                    zmq_send_annotation_update(afl, el->id, 1, contender+1);
                  }
                }

                {
                  int64_t overflow = el->shm_addr->result.best_values[4];
                  if (overflow) {
                    zmq_send_annotation_update(afl, el->id, 2, 0);
                  }
                  int64_t contender = el->shm_addr->result.best_values[5];
                  int64_t cur_best = (int64_t)el->cur_best.best_values[5];
                  if (contender < cur_best || cur_best == INT64_MIN) {
                    if (cur_best == INT64_MIN) {
                      candidate = 1;
                    }
                    el->cur_best.best_values[5] = contender;
                    improvement += 1;
                    ann_best_for_pos[2] = 1;
                    zmq_send_annotation_update(afl, el->id, 2, contender+1);
                  }
                }

                {
                  int64_t overflow = el->shm_addr->result.best_values[6];
                  if (overflow) {
                    zmq_send_annotation_update(afl, el->id, 3, 0);
                  }
                  int64_t contender = el->shm_addr->result.best_values[7];
                  int64_t cur_best = (int64_t)el->cur_best.best_values[7];
                  if (contender < cur_best || cur_best == INT64_MIN) {
                    if (cur_best == INT64_MIN) {
                      candidate = 1;
                    }
                    el->cur_best.best_values[7] = contender;
                    improvement += 1;
                    ann_best_for_pos[3] = 1;
                    zmq_send_annotation_update(afl, el->id, 3, contender+1);
                  }
                }
              }
              break;
            case ANN_MIN_CONTEXT:
              {
                if (num_writes > 0) {
                  for (int i = 0; i < ANNOTATION_RESULT_SIZE; i++) {
                    uint64_t contender = el->shm_addr->result.best_values[i];
                    if (contender < el->cur_best.best_values[i]) {
                      if (el->cur_best.best_values[i] == UINT64_MAX) {
                        candidate = 1;
                      }
                      el->cur_best.best_values[i] = contender;
                      improvement += 1;
                      if (i > el->max_pos) { el->max_pos = i; }
                      ann_best_for_pos[i] = 1;
                      zmq_send_annotation_update(afl, el->id, i, contender);
                    }
                  }
                }
              }
              break;
            case ANN_SET:
              {
                uint8_t * bitmap = el->shm_addr->result.set_hash_map;
                uint8_t * cur_best_map = el->cur_best.set_hash_map;
                for(int i = 0; i < sizeof(el->shm_addr->result.set_hash_map); i++) {
                  int cur_best = __builtin_popcount(cur_best_map[i]);
                  int contender = __builtin_popcount(cur_best_map[i] | bitmap[i]);
                  if (contender > cur_best) {
                      if (el->times_improved == 0) {
                        candidate = 1;
                      }
                      el->cur_best.set_hash_map[i] |= bitmap[i];
                      improvement += contender-cur_best;
                  }
                }
                if (improvement) {
                  zmq_send_annotation_update(afl, el->id, 0, improvement);
                }
              }
              break;
            case ANN_EDGE_COV:
              {
                if (!el->initialized) {
                  hne = el->id;
                  el->initialized = 1;
                  zmq_send_annotation_update(afl, el->id, 0, 1);
                }
              }
              break;
            case ANN_EDGE_MEM_COV:
              {
                uint8_t * bitmap = el->shm_addr->result.set_hash_map;
                uint8_t * cur_best_map = el->cur_best.set_hash_map;
                for(int i = 0; i < sizeof(el->shm_addr->result.set_hash_map); i++) {
                  int cur_best = __builtin_popcount(cur_best_map[i]);
                  int contender = __builtin_popcount(cur_best_map[i] | bitmap[i]);
                  if (contender > cur_best) {
                      el->cur_best.set_hash_map[i] |= bitmap[i];
                      improvement += contender-cur_best;
                  }
                }
                if (improvement) {
                  zmq_send_annotation_update(afl, el->id, 0, improvement);
                  hne = el->id;
                }
                improvement = 0; // not a normal annotation, it does not get own queue files
              }
              break;
            case ANN_META_NODE:
              {
                if (num_writes > 0) {
                  uint64_t contender = el->shm_addr->result.best_values[0];
                  if (knows_hash(el, contender)) {
                    break;
                  }
                  uint64_t * contender_ptr = malloc(sizeof(contender));
                  *contender_ptr = contender;
                  list_append(&el->meta_node_hashes, contender_ptr);
                  improvement += 1;
                  zmq_send_annotation_update(afl, el->id, 0, contender);
                }
              }
              break;
            default:
              FATAL("Unknown annotation type: %d", el->type);
          }
        }
        if (improvement) {
          ia = 1;
          el->times_improved += 1;
          el->total_times_improved += improvement;

          queue_fn = alloc_printf("%s/queue/id:%06u,%s,ann:%d,impr:%d", afl->out_dir,
                                  afl->total_queued_paths, describe_op(afl, 0, -1),
                                  el->id, el->times_improved);

          {
            struct queue_entry *q = add_to_queue(afl, queue_fn, len, 0, el, candidate, ann_best_for_pos,
                        /* do not update level */ 1);
            q->trim_done = 1;  // As trimming only checks the aflpp instrumentation,
                               // trimming can remove important information needed for annotations

            if(calibrate_case(afl, q, mem, afl->queue_cycle - 1, 0) == FSRV_RUN_ERROR) {
              FATAL("Unable to execute target application");
            }

            fd = open(queue_fn, O_WRONLY | O_CREAT | O_EXCL, 0600);
            if (unlikely(fd < 0)) PFATAL("Unable to create '%s'", queue_fn);
            ck_write(fd, mem, len, queue_fn);
            close(fd);

            // if not initialized we are not fuzzing a queue file for this annotation
            // as this annotation can not have any queue files
            // we only wanted to get a first value for this annotation which we now found
            // disable this annotation to minimize runtime overhead
            if (!el->initialized) {  
              el->initialized = 1;
              disable_annotation(afl, el);
              LIST_REMOVE_CURRENT_EL_IN_FOREACH();
            }

            // some annotations can create an unbounded amount of queue files
            // ignore them if their number gets too large
            if ((el->type == ANN_SET && el->num_corresponding_queue_files > 1024) 
                || (el->type == ANN_META_NODE && el->num_corresponding_queue_files > 10000)) {
                  el->ignored = 1;
              disable_annotation(afl, el);
              LIST_REMOVE_CURRENT_EL_IN_FOREACH();
            }
                 

            zmq_send_file_path(afl, q);
          }
        }
      });
    }

    /* Keep if there are new bits in the map is improved,
       add to queue for future fuzzing, etc. */
    hnb = has_new_bits(afl, afl->virgin_bits);
      
    if (!(hnb || (hne > -1))) {

      if (unlikely(afl->crash_mode)) { ++afl->total_crashes; }
      return ia;

    }

#ifndef SIMPLE_FILES

    queue_fn = alloc_printf("%s/queue/id:%06u,%s", afl->out_dir,
                            afl->total_queued_paths, describe_op(afl, hnb, hne));

#else

    queue_fn =
        alloc_printf("%s/queue/id_%06u", afl->out_dir, afl->queued_paths);

#endif                                                    /* ^!SIMPLE_FILES */

    {
      struct queue_entry *q = add_to_queue(afl, queue_fn, len, 0, NULL, 0, NULL, hnb==0);
      if (hne > -1) {
        q->trim_done = 1;  // As trimming only checks the aflpp instrumentation,
                            // trimming can remove important information needed for annotations
      }

      if (hnb == 2) {

        afl->queue_top->has_new_cov = 1;
        ++afl->queued_with_cov;

      }

      afl->queue_top->exec_cksum = cksum;

      /* Try to calibrate inline; this also calls update_bitmap_score() when
        successful. */

      res = calibrate_case(afl, afl->queue_top, mem, afl->queue_cycle - 1, 0);

      if (unlikely(res == FSRV_RUN_ERROR)) {

        FATAL("Unable to execute target application");

      }

      fd = open(queue_fn, O_WRONLY | O_CREAT | O_EXCL, 0600);
      if (unlikely(fd < 0)) { PFATAL("Unable to create '%s'", queue_fn); }
      ck_write(fd, mem, len, queue_fn);
      close(fd);

      zmq_send_file_path(afl, q);

      keeping = 1;
    }

  }

  switch (fault) {

    case FSRV_RUN_TMOUT:

      /* Timeouts are not very interesting, but we're still obliged to keep
         a handful of samples. We use the presence of new bits in the
         hang-specific bitmap as a signal of uniqueness. In "dumb" mode, we
         just keep everything. */

      ++afl->total_tmouts;

      if (afl->unique_hangs >= KEEP_UNIQUE_HANG) { return keeping; }

      if (likely(!afl->dumb_mode)) {

#ifdef WORD_SIZE_64
        simplify_trace(afl, (u64 *)afl->fsrv.trace_bits);
#else
        simplify_trace(afl, (u32 *)afl->fsrv.trace_bits);
#endif                                                     /* ^WORD_SIZE_64 */

        if (!has_new_bits(afl, afl->virgin_tmout)) { return keeping; }

      }

      ++afl->unique_tmouts;

      /* Before saving, we make sure that it's a genuine hang by re-running
         the target with a more generous timeout (unless the default timeout
         is already generous). */

      if (afl->fsrv.exec_tmout < afl->hang_tmout) {

        u8 new_fault;
        write_to_testcase(afl, mem, len);
        new_fault = fuzz_run_target(afl, &afl->fsrv, afl->hang_tmout);

        /* A corner case that one user reported bumping into: increasing the
           timeout actually uncovers a crash. Make sure we don't discard it if
           so. */

        if (!afl->stop_soon && new_fault == FSRV_RUN_CRASH) {

          goto keep_as_crash;

        }

        if (afl->stop_soon || new_fault != FSRV_RUN_TMOUT) { return keeping; }

      }

#ifndef SIMPLE_FILES

      snprintf(fn, PATH_MAX, "%s/hangs/id:%06llu,%s", afl->out_dir,
               afl->unique_hangs, describe_op(afl, 0, -1));

#else

      snprintf(fn, PATH_MAX, "%s/hangs/id_%06llu", afl->out_dir,
               afl->unique_hangs);

#endif                                                    /* ^!SIMPLE_FILES */

      ++afl->unique_hangs;

      afl->last_hang_time = get_cur_time();

      break;

    case FSRV_RUN_CRASH:

    keep_as_crash:

      /* This is handled in a manner roughly similar to timeouts,
         except for slightly different limits and no need to re-run test
         cases. */

      ++afl->total_crashes;

      if (afl->unique_crashes >= KEEP_UNIQUE_CRASH) { return keeping; }

      if (likely(!afl->dumb_mode)) {

#ifdef WORD_SIZE_64
        simplify_trace(afl, (u64 *)afl->fsrv.trace_bits);
#else
        simplify_trace(afl, (u32 *)afl->fsrv.trace_bits);
#endif                                                     /* ^WORD_SIZE_64 */

        if (!has_new_bits(afl, afl->virgin_crash)) { return keeping; }

      }

      if (unlikely(!afl->unique_crashes)) { write_crash_readme(afl); }

#ifndef SIMPLE_FILES

      snprintf(fn, PATH_MAX, "%s/crashes/id:%06llu,sig:%02u,%s", afl->out_dir,
               afl->unique_crashes, afl->fsrv.last_kill_signal,
               describe_op(afl, 0, -1));

#else

      snprintf(fn, PATH_MAX, "%s/crashes/id_%06llu_%02u", afl->out_dir,
               afl->unique_crashes, afl->last_kill_signal);

#endif                                                    /* ^!SIMPLE_FILES */

      ++afl->unique_crashes;
      if (unlikely(afl->infoexec)) {

        // if the user wants to be informed on new crashes - do that
#if !TARGET_OS_IPHONE
        // we dont care if system errors, but we dont want a
        // compiler warning either
        // See
        // https://stackoverflow.com/questions/11888594/ignoring-return-values-in-c
        (void)(system(afl->infoexec) + 1);
#else
        WARNF("command execution unsupported");
#endif

      }

      afl->last_crash_time = get_cur_time();
      afl->last_crash_execs = afl->fsrv.total_execs;

      break;

    case FSRV_RUN_ERROR:
      FATAL("Unable to execute target application");

    default:
      return keeping;

  }

  /* If we're here, we apparently want to save the crash or hang
     test case, too. */

  fd = open(fn, O_WRONLY | O_CREAT | O_EXCL, 0600);
  if (unlikely(fd < 0)) { PFATAL("Unable to create '%s'", fn); }
  ck_write(fd, mem, len, fn);
  close(fd);

  return keeping;

}

