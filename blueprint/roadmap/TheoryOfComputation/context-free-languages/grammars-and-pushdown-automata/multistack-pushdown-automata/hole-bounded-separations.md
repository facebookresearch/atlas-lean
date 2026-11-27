# Hole-bounded languages strictly extend scope-bounded ones and are incomparable with phase-bounded ones

There is a two-stack visibly MPDA over $\{a,b,c,d\}$ ($a,b$ push on stacks $1,2$; $c,d$ pop from them) whose $2$-hole-bounded language $L_{bh}$, which is also its full language, is not the $K$-scope-bounded, $K$-context-bounded, $K$-round-bounded or $K$-phase-bounded language of any visibly MPDA, for any $K$. Conversely, the language $L'=\{(ab)^{m}c^{m}d^{m}: m\ge 0\}$ is the $2$-phase-bounded (and full) language of a visibly MPDA but is not $K$-hole-bounded for any $K$. Hence hole-bounded and phase-bounded classes are incomparable.

## Proof sketch

$L_{bh}=\{a^n b^n\,a^{p_1}c^{p_1+1}b^{p_1'}d^{p_1'+1}\cdots a^{p_n}c^{p_n+1}b^{p_n'}d^{p_n'+1}\}$: every accepting run opens one hole for the $a^n$ and one for the $b^n$, and the rest is well-nested factors followed by single pops, so it is $2$-hole-bounded; the words $w_m=a^m b^m (ac^2bd^2)^m$ need scope $2m$, and the number of phases is unbounded as well. For $L'$, after reading $(ab)^m$ the pending pushes alternate between the two stacks, creating $2m$ holes; visibility forces every accepting run to have this shape.

## Depends on

- [Holes and hole-bounded sequences](hole-bounded-sequences.md)
- [Context-, round-, phase- and scope-bounded runs](bounded-context-classes.md)

## Proof depends on

- [Scope-bounded and round-bounded runs are hole-bounded](scope-bounded-runs-are-hole-bounded.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), arXiv:2002.05950, 2020, Proposition 2 and its proof.
