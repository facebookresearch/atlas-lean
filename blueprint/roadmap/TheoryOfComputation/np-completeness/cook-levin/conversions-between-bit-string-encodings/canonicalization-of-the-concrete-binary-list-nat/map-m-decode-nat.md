# Decoding natural-number payloads never fails

A natural number is coded by its binary code (binary digits, least significant first, no trailing zero), and the
decoder of natural numbers is the total map $D$ of [payload normalization](../normalizing-the-total-binary-natural-number-deco/normalize-nat-eq-encode-decode.md),
which reads a trailing $0$ as if a $1$ followed it.

For every list $(p^1, \ldots, p^k)$ of bit strings, decoding each $p^i$ as a natural number succeeds for all $i$
and gives $(D(p^1), \ldots, D(p^k))$, also when the $p^i$ are not binary codes.
