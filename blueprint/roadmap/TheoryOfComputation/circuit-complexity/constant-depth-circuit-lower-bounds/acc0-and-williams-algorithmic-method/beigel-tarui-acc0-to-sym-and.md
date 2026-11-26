# Yao and Beigel–Tarui: ACC0 circuits are quasi-polynomial SYM ∘ AND circuits

Let $C$ be a circuit on $n$ inputs of size $s$ and depth $d$ with $\neg$, unbounded fan-in $\wedge,\vee$ and $\mathrm{MOD}_m$ gates ($m\ge1$). Then $C$ computes the same function as a $\mathrm{SYM}\circ\mathrm{AND}$ circuit of fan-in at most $(2B)^{5^{d(m+2)}}$ and at most $2^{(2B)^{5^{d(m+2)}}}$ AND gates, where $B=3\bigl((m+1)^2+\lfloor\log_2(n+s)\rfloor+2\bigr)$. For fixed $d$ and $m$ this is fan-in $\mathrm{polylog}(n+s)$ and size $2^{\mathrm{polylog}(n+s)}$; hence every language in $\mathsf{ACC}^0$ has $\mathrm{SYM}\circ\mathrm{AND}$ circuits of polylogarithmic fan-in and quasi-polynomial size.

## Proof sketch

Replace AND/OR gates by probabilistic low-degree modular polynomials (Razborov–Smolensky style), derandomize by summing over a small seed set, and collapse the resulting towers of modular polynomial layers into a single symmetric function of a sum of monomials, using modulus-amplifying polynomials (Toda-type) to push all moduli to the top.

## Depends on

- [SYM ∘ AND circuits](sym-and-circuits.md)
- [The class $\mathsf{ACC}^0$](../../../complexity-classes/time-and-space-complexity-classes/acc0.md)

## Proof depends on

- [Razborov–Smolensky polynomial approximation of AC0[p]](../razborovsmolensky-polynomial-approximation-of.md)

## Sources

- Richard Beigel, Jun Tarui, "On ACC", Computational Complexity, 1994.
- Ryan Williams, "Nonuniform ACC Circuit Lower Bounds", Journal of the ACM, 2014.
