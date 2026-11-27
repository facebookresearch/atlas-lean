# Fearnley–Goldberg–Hollender–Savani: KKT on the unit square is PPAD ∩ PLS-hard, already for promise instances

There is a polynomial-time many-one reduction from EITHER-SOLUTION(END-OF-LINE, ITER) to KKT with domain fixed to $D=[0,1]^2$. Consequently KKT on $[0,1]^2$ is $\mathsf{PPAD}\cap\mathsf{PLS}$-hard, and the hardness holds for the promise version, since the constructed instances have no violations. The hardness requires $\varepsilon$ and $L$ in binary with at least one of them exponential in the input size: if both are given in unary, an $\varepsilon$-KKT point on $[0,1]^n$ is found in polynomial time by running projected gradient descent.

## Proof sketch

Build $f$ on $[0,N]^2$ with the staircase embedding of the END-OF-LINE instance, insert PLS-Labyrinths at all green/orange meeting points, interpolate bicubically, and rescale to $[0,1]^2$ (multiplying the Lipschitz constant by a power of $N$). By the two lemmas every $\varepsilon$-KKT point yields an END-OF-LINE or an ITER solution in polynomial time. For unary parameters, each projected step with $\eta=1/L$ decreases $f$ by $\Omega(\varepsilon^2/L)$ until an $\varepsilon$-KKT point is reached, and $f$ varies by at most $L\sqrt n$ on the cube, so polynomially many steps suffice.

## Depends on

- [The KKT search problem for smooth objectives on bounded polytopes with Taylor-violation witnesses](kkt-search-problem.md)
- [ITER and the EITHER-SOLUTION combinator for building PPAD ∩ PLS-complete problems](iter-and-either-solution.md)

## Proof depends on

- [EITHER-SOLUTION(END-OF-LINE, ITER) is PPAD ∩ PLS-complete](either-solution-eol-iter-complete.md)
- [PLS-Labyrinth gadget with bicubic interpolation: unavoidable KKT points at colour changes encode ITER solutions](pls-labyrinth-gadget.md)
- [Staircase embedding of END-OF-LINE into a planar descent landscape with green descending and orange ascending paths](staircase-embedding-green-orange-paths.md)

## Sources

- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
