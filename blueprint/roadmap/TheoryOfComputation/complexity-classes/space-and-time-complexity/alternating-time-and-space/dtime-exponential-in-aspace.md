# Deterministic time 2^{O(s)} is contained in alternating space s

Let $s$ be space-constructible with $\lfloor\log_2 n\rfloor\le s(n)$. Then for every constant $c$,

$$
\mathsf{DTIME}\bigl(2^{c\,s(n)}\bigr)\subseteq\mathsf{ASPACE}(s(n)),
$$

with an alternating machine all of whose branches halt and stay within $O(s(n))$ work cells.

## Proof sketch

Write the step count $T=2^{O(s)}$ in binary within space $O(s)$. The alternating machine plays the local circuit-value game on the $T\times T$ tableau of the deterministic machine: it stores only a time, a position and a claimed cell value, each in $O(s)$ bits, and the universal player challenges one of the predecessor cells.

## Depends on

- [Alternating time and space classes ATIME, ASPACE, AP, APSPACE and AL](alternating-time-and-space-classes.md)
- [Deterministic time classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dtime.md)

## Proof depends on

- [The Circuit Value Problem is P-complete](../../../completeness-other-classes/circuit-value-problem/cvp-p-complete.md)

## Sources

- Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer, "Alternation", Journal of the ACM 28(1), 1981.
