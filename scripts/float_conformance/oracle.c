/* Copyright (c) Meta Platforms, Inc. and affiliates.
 * Licensed under the LICENSE file in the root directory of this source tree.
 * Binary64 add/mul only; header-backed MPFR and separate SSE2 operations. */
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <fenv.h>
#include <float.h>
#include <inttypes.h>
#include <mpfr.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <xmmintrin.h>
#if !defined(__x86_64__) || !defined(__linux__)
#error "This diagnostic initially supports x86_64 Linux only"
#endif
_Static_assert(sizeof(double) == 8 && DBL_MANT_DIG == 53 &&
               DBL_MAX_EXP == 1024, "binary64 required");
static uint64_t add_calls, mul_calls, exact_calls;
static void fail(const char *message) {
  fprintf(stderr, "oracle failed: %s\n", message);
  exit(1);
}
static double decode(uint64_t bits) {
  double value;
  memcpy(&value, &bits, sizeof(value));
  return value;
}
static uint64_t encode(double value) {
  uint64_t bits;
  memcpy(&bits, &value, sizeof(bits));
  return bits;
}
static int finite_bits(uint64_t u) {
  return (u & UINT64_C(0x7ff0000000000000)) !=
         UINT64_C(0x7ff0000000000000);
}
static int nan_bits(uint64_t u) {
  return !finite_bits(u) && (u & UINT64_C(0xfffffffffffff)) != 0;
}
static void environment(void) {
  unsigned short cw;
  __asm__("fnstcw %0" : "=m"(cw));
  if (fegetround() != FE_TONEAREST || (_mm_getcsr() & 0xe040) ||
      (cw & 0xc00)) fail("require RNE with FTZ=0 and DAZ=0");
}
__attribute__((noinline)) uint64_t hw_add(uint64_t a, uint64_t b) {
  volatile double result = decode(a) + decode(b);
  ++add_calls;
  return encode(result);
}
__attribute__((noinline)) uint64_t hw_mul(uint64_t a, uint64_t b) {
  volatile double result = decode(a) * decode(b);
  ++mul_calls;
  return encode(result);
}
__attribute__((noinline)) void oracle_pair(
    mpfr_t x, mpfr_t y, mpfr_t z, uint64_t a, uint64_t b,
    uint64_t *sum, uint64_t *product) {
  if (mpfr_set_d(x, decode(a), MPFR_RNDN) ||
      mpfr_set_d(y, decode(b), MPFR_RNDN)) fail("input was not exact");
  uint64_t aa = encode(mpfr_get_d(x, MPFR_RNDN));
  uint64_t bb = encode(mpfr_get_d(y, MPFR_RNDN));
  if ((a != aa && !(nan_bits(a) && nan_bits(aa))) ||
      (b != bb && !(nan_bits(b) && nan_bits(bb)))) fail("input roundtrip");
  int t = mpfr_add(z, x, y, MPFR_RNDN);
  if (finite_bits(a) && finite_bits(b)) {
    if (t) fail("inexact intermediate add");
    ++exact_calls;
  }
  *sum = encode(mpfr_get_d(z, MPFR_RNDN));
  t = mpfr_mul(z, x, y, MPFR_RNDN);
  if (finite_bits(a) && finite_bits(b)) {
    if (t) fail("inexact intermediate multiply");
    ++exact_calls;
  }
  *product = encode(mpfr_get_d(z, MPFR_RNDN));
}
static uint64_t number(char **cursor) {
  char *start = *cursor, *end;
  if (*start < '0' || *start > '9') fail("invalid unsigned integer");
  errno = 0;
  uint64_t value = strtoull(start, &end, 10);
  if (errno == ERANGE || end == start) fail("integer out of range");
  *cursor = end;
  return value;
}
int main(int argc, char **argv) {
  if (argc != 2) fail("expected input file");
  environment();
  unsigned before = _mm_getcsr();
  if (strcmp(MPFR_VERSION_STRING, mpfr_get_version()))
    fail("MPFR header/runtime version mismatch");
  if (mpfr_get_emin() >= -2200 || mpfr_get_emax() <= 2200)
    fail("MPFR exponent range too small");
  mpfr_t x, y, z;
  mpfr_init2(x, 2200); mpfr_init2(y, 2200); mpfr_init2(z, 2200);
  FILE *input = fopen(argv[1], "r");
  if (!input) fail("cannot open input");
  char *line = NULL;
  size_t capacity = 0, count = 0;
  ssize_t length;
  while ((length = getline(&line, &capacity, input)) >= 0) {
    if (++count > 16384 || length > 128) fail("input bounds exceeded");
    char *cursor = line;
    uint64_t index = number(&cursor);
    if (*cursor++ != ' ') fail("malformed input");
    uint64_t a = number(&cursor);
    if (*cursor++ != ' ') fail("malformed input");
    uint64_t b = number(&cursor);
    if (index != count - 1 || strcmp(cursor, "\n")) fail("malformed row");
    uint64_t sum, product;
    oracle_pair(x, y, z, a, b, &sum, &product);
    uint64_t hardware_sum = hw_add(a, b);
    uint64_t hardware_product = hw_mul(a, b);
    if (printf("%" PRIu64 "|%" PRIu64 "|%" PRIu64 "|%" PRIu64
               "|%" PRIu64 "|%" PRIu64 "|%" PRIu64 "\n",
               index, a, b, sum, product, hardware_sum,
               hardware_product) < 0) fail("output write failed");
  }
  if (ferror(input) || !count || add_calls != count || mul_calls != count)
    fail("incomplete input or execution");
  if (fclose(input) || fflush(stdout)) fail("I/O failure");
  environment();
  fprintf(stderr, "{\"pairs\":%zu,\"hardware_add_calls\":%" PRIu64
          ",\"hardware_mul_calls\":%" PRIu64 ",\"exact_ops\":%" PRIu64
          ",\"precision\":2200,\"mpfr_header\":\"%s\","
          "\"mpfr_runtime\":\"%s\",\"gmp_runtime\":\"%s\","
          "\"mpfr_struct_bytes\":%zu,\"mxcsr_before\":%u,"
          "\"mxcsr_after\":%u}\n", count, add_calls, mul_calls,
          exact_calls, MPFR_VERSION_STRING, mpfr_get_version(),
          gmp_version, sizeof(mpfr_t), before, _mm_getcsr());
  mpfr_clear(x); mpfr_clear(y); mpfr_clear(z); free(line);
  return 0;
}
