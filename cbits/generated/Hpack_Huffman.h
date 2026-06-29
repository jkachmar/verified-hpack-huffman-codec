/*
 * GENERATED from the verified F* sources in fstar/.
 * Do not edit by hand -- regenerate with: make -C fstar generate
 */

#ifndef Hpack_Huffman_H
#define Hpack_Huffman_H

#include "krmllib.h"

uint32_t Hpack_Huffman_encode_len(uint8_t *src, uint32_t len);

uint32_t Hpack_Huffman_encode(uint8_t *src, uint32_t len, uint8_t *dst);

int32_t
Hpack_Huffman_decode(
  uint8_t *src,
  uint32_t src_len,
  uint8_t *dst,
  uint32_t dst_cap,
  uint32_t *out_len
);


#define Hpack_Huffman_H_DEFINED
#endif /* Hpack_Huffman_H */
