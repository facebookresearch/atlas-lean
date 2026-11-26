# d-DNNF is not polynomially closed under negation, given cubic edge expanders

For every cubic graph $G$ on $n\ge2$ vertices with a proper $3$-edge-colouring that is a balanced-cut $\gamma$-edge expander, $f_G$ has a d-DNNF with at most $150n+50$ nodes, while every DNNF computing $\neg f_G$ has at least $(48/47)^{\gamma n/126}$ nodes. Hence, if such expanders exist with $\gamma>0$ for unboundedly many $n$, the class of functions with polynomial-size d-DNNFs is not closed under negation (there are $f$ with linear-size d-DNNFs whose negations need DNNFs of size $2^{\Omega(n)}$).

## Proof sketch

Upper bound: $f_G$ is a disjunction over the colour $c$ that is missing of the functions 'some edge, and no induced edge of colour $c$'; each is a conjunction of local constraints on matching edges of colour $c$ (no edge of that colour has both endpoints selected) and is compiled deterministically, with disjointness arranged by fixing the least missing colour. Lower bound: every balanced rectangle inside $f_G^{-1}(0)=(\neg f_G)^{-1}(1)$ is small, because across a balanced cut of an edge expander many edges cross and the zero set forces a violation that is incompatible with a product structure; the rectangle-cover bound for DNNFs then gives exponential size.

## Depends on

- [The some-but-not-all-colours function of an edge-coloured cubic graph](some-but-not-all-colours-function.md)
- [Balanced multi-partition rectangle covers](multi-partition-rectangle-covers.md)

## Proof depends on

- [DNNF size bounds the multi-partition rectangle cover number](dnnf-size-bounds-rectangle-cover-number.md)
- [Read-once branching programs compile into d-DNNFs](read-once-branching-programs-as-d-dnnfs.md)

## Sources

- Marcelo Arenas, Oliver Broadrick, Vincent Liew, Guy Van den Broeck, "d-DNNF is Not Polynomially Closed Under Negation", STOC 2027 submission 1318, 2026.
