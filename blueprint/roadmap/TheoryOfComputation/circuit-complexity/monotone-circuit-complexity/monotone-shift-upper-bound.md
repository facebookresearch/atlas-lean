# Monotone cyclic shift in L(A) + O(qn log n) gates

Let $\alpha$ be an injective antichain code and suppose a monotone circuit with $L(A)$ binary gates computes all the monomials $Y\mapsto[\alpha(k)\le Y]$. Then the monotone cyclic shift operator $S_{q,\alpha}$ has a monotone circuit with at most $L(A)+4qn\lceil\log_2 n\rceil$ binary gates. For the one-hot code ($L(A)=0$) and the dual-rail binary code this gives $O(qn\log n)$.

## Proof sketch

Decompose a shift by $k$ into shifts by the powers of two in the binary expansion of $k$, each controlled by a monotone selector derived from the antichain monomials; each of the $\lceil\log_2 n\rceil$ stages costs $O(qn)$ gates.

## Depends on

- [Monotone cyclic shift and permutation operators](monotone-cyclic-shift-operator.md)

## Sources

- Igor S. Sergeev, "On the Monotone Complexity of the Shift Operator", 2020.
