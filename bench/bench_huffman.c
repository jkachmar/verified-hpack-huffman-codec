/* Micro-benchmark for the verified HPACK Huffman codec (no Haskell / GHC).
 * Reproduces the encode/decode figures in ARCHITECTURE.md's Performance table
 * for the same fixtures, using clock_gettime. Indicative, single-threaded. */

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include "hpack_huffman.h"

static double now_ns(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec * 1e9 + (double)t.tv_nsec;
}

static void bench(const char *name, const uint8_t *in, size_t len) {
    uint8_t enc[8192], dec[8192];
    size_t out = 0;
    size_t elen = hpack_huffman_encode(in, len, enc);
    const long N = 2000000, W = 50000;

    for (long i = 0; i < W; i++) { volatile size_t e = hpack_huffman_encode(in, len, enc); (void)e; }
    double t0 = now_ns();
    for (long i = 0; i < N; i++) hpack_huffman_encode(in, len, enc);
    double t1 = now_ns();

    for (long i = 0; i < W; i++) hpack_huffman_decode(enc, elen, dec, sizeof dec, &out);
    double t2 = now_ns();
    for (long i = 0; i < N; i++) hpack_huffman_decode(enc, elen, dec, sizeof dec, &out);
    double t3 = now_ns();

    printf("  %-22s %4zuB -> %4zuB   encode %6.1f ns   decode %6.1f ns\n",
           name, len, elen, (t1 - t0) / (double)N, (t3 - t2) / (double)N);
}

int main(void) {
    /* fixtures mirroring ARCHITECTURE.md's table */
    const char *www = "www.example.com";                                 /* 15 B */
    uint8_t mixed[128];
    {   const char *s = "The quick brown fox jumps over the lazy dog. "
                        "HTTP/2! GET /api/v1/users?page=1&limit=20 :authority=x";
        for (size_t i = 0; i < sizeof mixed; i++) mixed[i] = (uint8_t)s[i % strlen(s)]; }
    uint8_t a256[256]; memset(a256, 0x61, sizeof a256);                   /* 256 B of 'a' */

    printf("verified HPACK Huffman codec — micro-benchmark (clock_gettime, single-threaded)\n");
    bench("www.example.com",  (const uint8_t *)www, strlen(www));
    bench("mixed ascii",      mixed, sizeof mixed);
    bench("uniform 'a'",      a256, sizeof a256);
    return 0;
}
