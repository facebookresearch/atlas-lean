# Hole-bounded languages strictly extend scope-bounded ones and are incomparable with phase-bounded ones

There is a two-stack visibly MPDA over $\{a,b,c,d\}$ ($a,b$ push on stacks $1,2$; $c,d$ pop from them) whose $2$-hole-bounded language $L_{bh}$, which is also its full language, is not the $K$-scope-bounded, $K$-context-bounded or $K$-round-bounded language of any visibly MPDA, for any $K$. Conversely, the language $L'=\{(ab)^{m}c^{m}d^{m}: m\ge 0\}$ is the $2$-phase-bounded (and full) language of a visibly MPDA but is not $K$-hole-bounded for any $K$. Hence hole-bounded and phase-bounded classes are incomparable.

## Proof sketch

For $L_{bh}$, witnesses $w_m$ require scope (or number of contexts) growing with $m$ while keeping at most two holes. For $L'$, after reading $(ab)^m$ the pending pushes alternate between the two stacks, creating $2m$ holes; visibility forces every accepting run to have this shape.

## Depends on

- [Holes and hole-bounded sequences](hole-bounded-sequences.md)
- [Context-, round-, phase- and scope-bounded runs](bounded-context-classes.md)

## Proof depends on

- [Scope-bounded and round-bounded runs are hole-bounded](scope-bounded-runs-are-hole-bounded.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), arXiv:2002.05950, 2020, Proposition 2.
