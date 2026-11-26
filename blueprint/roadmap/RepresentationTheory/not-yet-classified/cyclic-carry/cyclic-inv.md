# Cyclic Inv

The cyclic sum of a two-variable function `c`: the sum of `c (s ^ i, s)`
over `i < orderOf s`, so the first variable ranges over the powers of `s` and
the second is fixed at `s`. The definition is a plain sum: it takes no
hypothesis on `s` or `c` and does not assert that the result is fixed by `G`.
When `s` does not generate `G`, the first variable still ranges only over the
powers of `s`; when `s` has infinite order, `orderOf s = 0`, the sum is empty
and the value is `0`.
