# Balanced multi-partition rectangle covers

For a set $X$ of $n$ variables, a *balanced rectangle* is a function of the form $g(x)=g_1(x_Y)\wedge g_2(x_{X\setminus Y})$ for some partition $(Y,X\setminus Y)$ with $n/3\le|Y|\le2n/3$. A *balanced multi-partition rectangle cover* of $f$ is a family of balanced rectangles, each with its own partition, whose disjunction is $f$ (each rectangle is contained in $f^{-1}(1)$ and they cover it). The cover number of $f$ is the least size of such a cover.

## Depends on

- [Negation normal form circuits, DNNF and d-DNNF](nnf-dnnf-and-d-dnnf.md)
- [Rectangle lemma](../../../../communication-complexity/deterministic-communication-protocols/transcript-eq-iff.md)

## Sources

- Simone Bova, Florent Capelli, Stefan Mengel, Friedrich Slivovsky, "Knowledge Compilation Meets Communication Complexity", Proceedings of the Twenty-Fifth International Joint Conference on Artificial Intelligence (IJCAI 2016), 2016.
