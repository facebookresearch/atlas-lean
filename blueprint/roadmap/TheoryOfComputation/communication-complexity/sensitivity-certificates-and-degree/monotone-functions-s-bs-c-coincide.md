# For monotone functions, sensitivity, block sensitivity and certificate complexity coincide

For every monotone $f : \{0,1\}^n \to \{0,1\}$: $C(f) = bs(f) = s(f)$, more precisely $C_b(f) \le s_b(f)$ for each $b$, and $D(f) \le s_0(f)\, s_1(f) \le s(f)^2$.

## Proof sketch

If $f(x) = 1$, take $y \le x$ of minimum weight with $f(y) = 1$. Every true bit of $y$ is sensitive at $y$, and the true bits of $y$ certify $x$ (anything above $y$ has value $1$), so $C(f, x) \le s_1(f)$. Dually for $f(x) = 0$. Then $D \le C_0 C_1$.

## Depends on

- [One-sided sensitivity, block sensitivity and certificate complexity](one-sided-complexity-measures.md)

## Proof depends on

- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002.
