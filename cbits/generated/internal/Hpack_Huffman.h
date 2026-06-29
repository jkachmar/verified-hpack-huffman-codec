/*
 * GENERATED from the verified F* sources in fstar/.
 * Do not edit by hand -- regenerate with: make -C fstar generate
 */

#ifndef internal_Hpack_Huffman_H
#define internal_Hpack_Huffman_H

#include "krmllib.h"

#include "../Hpack_Huffman.h"

int32_t
Hpack_Huffman_Lowstar_Dfa_dfa_loop(
  uint8_t *src0,
  uint8_t *dst0,
  uint32_t src_len0,
  uint32_t dst_cap0,
  uint32_t g0,
  uint32_t cur0,
  uint32_t written0,
  uint32_t *out_len0
);

uint64_t
Hpack_Huffman_Lowstar_Codec_sum_loop(uint8_t *src0, uint32_t len0, uint32_t i0, uint64_t acc0);

typedef struct K___uint32_t_uint32_t_uint64_t_s
{
  uint32_t fst;
  uint32_t snd;
  uint64_t thd;
}
K___uint32_t_uint32_t_uint64_t;

K___uint32_t_uint32_t_uint64_t
Hpack_Huffman_Lowstar_Codec_encode_loop(
  uint8_t *dst0,
  uint8_t *src0,
  uint32_t len0,
  uint32_t i0,
  uint32_t out0,
  uint32_t nbits0,
  uint64_t bits0
);


#define internal_Hpack_Huffman_H_DEFINED
#endif /* internal_Hpack_Huffman_H */
