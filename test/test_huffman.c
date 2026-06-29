/* C validation harness for the verified HPACK Huffman codec.
 *
 * Exercises the public C ABI (cbits/hpack_huffman.h) with no toolchain beyond a C
 * compiler: round-trips over every byte value, the RFC 7541 Appendix C.4 Huffman
 * string vectors (checking exact encoded bytes), and malformed-input rejection.
 * The F* proof is the real correctness guarantee; this is an independent,
 * dependency-free cross-check. Exits nonzero on any mismatch. */

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "hpack_huffman.h"

static int checks = 0, failures = 0;

/* encode src[0..len), decode it back, require exact recovery (+ encode_len agreement). */
static void roundtrip(const uint8_t *src, size_t len, const char *what) {
    uint8_t enc[8192], dec[8192];
    size_t out = 0;
    checks++;
    size_t elen  = hpack_huffman_encode(src, len, enc);
    size_t elen2 = hpack_huffman_encode_len(src, len);
    if (elen != elen2) {
        printf("FAIL [%s]: encode_len=%zu but encode wrote %zu\n", what, elen2, elen);
        failures++; return;
    }
    int rc = hpack_huffman_decode(enc, elen, dec, sizeof dec, &out);
    if (rc != 0 || out != len || memcmp(src, dec, len) != 0) {
        printf("FAIL [%s]: round-trip mismatch (rc=%d, out=%zu, want %zu)\n", what, rc, out, len);
        failures++; return;
    }
}

/* encode(s) must equal `exp` exactly, and decode(exp) must recover s (RFC vector). */
static void enc_vector(const char *s, const uint8_t *exp, size_t elen, const char *what) {
    uint8_t enc[256], dec[256];
    size_t out = 0, slen = strlen(s);
    checks++;
    size_t n = hpack_huffman_encode((const uint8_t *)s, slen, enc);
    if (n != elen || memcmp(enc, exp, elen) != 0) {
        printf("FAIL [%s]: encode produced %zu bytes, not the RFC vector\n", what, n);
        failures++; return;
    }
    int rc = hpack_huffman_decode(exp, elen, dec, sizeof dec, &out);
    if (rc != 0 || out != slen || memcmp(dec, s, slen) != 0) {
        printf("FAIL [%s]: decode of RFC vector mismatch (rc=%d, out=%zu)\n", what, rc, out);
        failures++; return;
    }
}

/* decode must reject (return -1) a malformed Huffman stream. */
static void reject(const uint8_t *src, size_t len, const char *what) {
    uint8_t dec[256];
    size_t out = 0;
    checks++;
    int rc = hpack_huffman_decode(src, len, dec, sizeof dec, &out);
    if (rc == 0) {
        printf("FAIL [%s]: expected rejection, but decode accepted (out=%zu)\n", what, out);
        failures++;
    }
}

int main(void) {
    /* 1. empty input */
    roundtrip((const uint8_t *)"", 0, "empty");

    /* 2. every single byte value 0x00..0xFF */
    for (int b = 0; b < 256; b++) { uint8_t x = (uint8_t)b; roundtrip(&x, 1, "single byte"); }

    /* 3. all 256 byte values in one buffer */
    { uint8_t all[256]; for (int b = 0; b < 256; b++) all[b] = (uint8_t)b;
      roundtrip(all, sizeof all, "all 256 bytes"); }

    /* 4. mixed / long / non-ASCII content */
    roundtrip((const uint8_t *)"The quick brown fox jumps over the lazy dog. HTTP/2!",
              52, "mixed ascii");
    { uint8_t r[1024]; memset(r, 0x61, sizeof r); roundtrip(r, sizeof r, "1024x 'a'"); }
    { uint8_t hi[300]; for (size_t i = 0; i < sizeof hi; i++) hi[i] = (uint8_t)(0x80 + (i % 0x60));
      roundtrip(hi, sizeof hi, "non-ascii run"); }

    /* 5. RFC 7541 Appendix C.4 Huffman string vectors (exact encoded bytes) */
    { static const uint8_t v[] = {0xf1,0xe3,0xc2,0xe5,0xf2,0x3a,0x6b,0xa0,0xab,0x90,0xf4,0xff};
      enc_vector("www.example.com", v, sizeof v, "RFC C.4.1 www.example.com"); }
    { static const uint8_t v[] = {0xa8,0xeb,0x10,0x64,0x9c,0xbf};
      enc_vector("no-cache", v, sizeof v, "RFC C.4.2 no-cache"); }
    { static const uint8_t v[] = {0x25,0xa8,0x49,0xe9,0x5b,0xa9,0x7d,0x7f};
      enc_vector("custom-key", v, sizeof v, "RFC C.4.3 custom-key"); }
    { static const uint8_t v[] = {0x25,0xa8,0x49,0xe9,0x5b,0xb8,0xe8,0xb4,0xbf};
      enc_vector("custom-value", v, sizeof v, "RFC C.4.3 custom-value"); }

    /* 6. malformed inputs the spec rejects */
    { static const uint8_t x[] = {0x00};                /* '0' (00000) then 000 — non-all-ones padding */
      reject(x, sizeof x, "invalid (zero-bit) padding"); }
    { static const uint8_t x[] = {0xff,0xff,0xff,0xff};  /* 30 ones reach the EOS symbol in-stream */
      reject(x, sizeof x, "in-stream EOS"); }

    printf("\n%d checks, %d failures\n", checks, failures);
    return failures ? 1 : 0;
}
