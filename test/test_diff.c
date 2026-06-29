/* Differential test: the verified codec vs. the hand-written nghttp2-derived
 * decoder it replaced (an independent implementation of the same RFC table,
 * vendored test-only as ref_huffman.c). Agreement on random inputs is strong
 * evidence both are correct — it would take a *compensating* bug in both to pass.
 *
 * Strong checks (valid data, unambiguous): the two encoders must produce identical
 * bytes, and each decoder must recover the plaintext from the other's encoding.
 * Weaker check (arbitrary bytes): when both decoders accept, their output must
 * match — but we do NOT require agreement on accept/reject, since the verified
 * decoder is strict per RFC 7541 while the reference may be more lenient on padding. */

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "hpack_huffman.h"                 /* verified codec: hpack_huffman_* */

/* the vendored reference (renamed symbols) */
size_t ref_hpack_huffman_encode(const uint8_t *src, size_t len, uint8_t *dst);
int    ref_hpack_huffman_decode(const uint8_t *src, size_t src_len,
                                uint8_t *dst, size_t dst_cap, size_t *out_len);

static uint64_t st = 0x9e3779b97f4a7c15ull;     /* fixed seed -> deterministic */
static uint32_t rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return (uint32_t)(st >> 32); }

int main(void) {
    int checks = 0, fails = 0;

    /* (1) valid plaintext: encoders agree byte-for-byte, decoders cross-recover */
    for (int it = 0; it < 300000; it++) {
        size_t len = rnd() % 64;
        uint8_t in[64]; for (size_t i = 0; i < len; i++) in[i] = (uint8_t)rnd();

        uint8_t e1[512], e2[512];
        size_t n1 = hpack_huffman_encode(in, len, e1);
        size_t n2 = ref_hpack_huffman_encode(in, len, e2);
        checks++;
        if (n1 != n2 || memcmp(e1, e2, n1) != 0) {
            printf("FAIL: encoders disagree (it=%d len=%zu: %zu vs %zu bytes)\n", it, len, n1, n2);
            fails++; continue;
        }
        uint8_t d1[64], d2[64]; size_t o1 = 0, o2 = 0;
        int r1 = hpack_huffman_decode(e2, n2, d1, sizeof d1, &o1);  /* ours <- ref's enc */
        int r2 = ref_hpack_huffman_decode(e1, n1, d2, sizeof d2, &o2);       /* ref  <- ours' enc */
        checks += 2;
        if (r1 != 0 || o1 != len || memcmp(d1, in, len) != 0) { printf("FAIL: verified decode(ref enc) it=%d\n", it); fails++; }
        if (r2 != 0 || o2 != len || memcmp(d2, in, len) != 0) { printf("FAIL: ref decode(verified enc) it=%d\n", it); fails++; }
    }

    /* (2) arbitrary bytes: when both accept, decoded output must match */
    for (int it = 0; it < 300000; it++) {
        size_t len = 1 + rnd() % 16;
        uint8_t in[16]; for (size_t i = 0; i < len; i++) in[i] = (uint8_t)rnd();
        uint8_t d1[64], d2[64]; size_t o1 = 0, o2 = 0;
        int r1 = hpack_huffman_decode(in, len, d1, sizeof d1, &o1);
        int r2 = ref_hpack_huffman_decode(in, len, d2, sizeof d2, &o2);
        checks++;
        if (r1 == 0 && r2 == 0 && (o1 != o2 || memcmp(d1, d2, o1) != 0)) {
            printf("FAIL: decoders accept but disagree on output (it=%d)\n", it); fails++;
        }
    }

    printf("\ndifferential vs reference: %d checks, %d failures\n", checks, fails);
    return fails ? 1 : 0;
}
