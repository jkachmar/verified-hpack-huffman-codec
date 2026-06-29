/*
 * HPACK Huffman encoding and decoding (RFC 7541 Appendix B).
 *
 * Thin FFI shim over the verified F* implementation (lowered to C by KaRaMeL;
 * see cbits/generated/, regenerated from fstar/). It bridges the
 * public size_t-based ABI that the Haskell FFI expects to the
 * generated uint32_t-based Hpack_Huffman_* symbols. No encoding or decoding
 * decision is made here — encode, encode_len, and the RFC 7541 §5.2 decoder all
 * live in the verified module.
 */

#include <stdint.h>
#include <stddef.h>

#include "generated/Hpack_Huffman.h"

/* The verified contracts require lengths below 2^27, which keeps the encoder's
 * bit total within its proven uint32/uint64 bounds and keeps the decoder's
 * 8*src_len bit index within uint32. KaRaMeL erases these preconditions from
 * the generated C, so we enforce them at the boundary. HTTP/2 frame-size limits
 * bound real HPACK string literals far below this; an over-large input is
 * refused rather than risk an unproven truncation. */
#define HPACK_HUFFMAN_MAX_LEN ((size_t)1 << 27)

size_t hpack_huffman_encode_len(const uint8_t *src, size_t len)
{
    if (len >= HPACK_HUFFMAN_MAX_LEN) return 0;
    return (size_t) Hpack_Huffman_encode_len((uint8_t *)src, (uint32_t)len);
}

size_t hpack_huffman_encode(const uint8_t *src, size_t len, uint8_t *dst)
{
    if (len >= HPACK_HUFFMAN_MAX_LEN) return 0;
    return (size_t) Hpack_Huffman_encode((uint8_t *)src, (uint32_t)len, dst);
}

int hpack_huffman_decode(
    const uint8_t *src, size_t src_len,
    uint8_t *dst, size_t dst_cap,
    size_t *out_len)
{
    uint32_t written = 0;
    uint32_t cap32;
    int32_t  rc;

    /* Keep src_len within the verified uint32 domain (the proof needs
     * 8*src_len < 2^30). */
    if (src_len >= HPACK_HUFFMAN_MAX_LEN) {
        *out_len = 0;
        return -1;
    }

    /* The verified decoder writes at most dst_cap bytes. Clamp the capacity into
     * uint32 for the call; the destination buffer is at least dst_cap bytes, so
     * the clamped value still satisfies the precondition (cap <= buffer length). */
    cap32 = dst_cap > UINT32_MAX ? UINT32_MAX : (uint32_t)dst_cap;

    rc = Hpack_Huffman_decode(
        (uint8_t *)src, (uint32_t)src_len, dst, cap32, &written);

    *out_len = (size_t)written;
    return rc == 0 ? 0 : -1;
}
