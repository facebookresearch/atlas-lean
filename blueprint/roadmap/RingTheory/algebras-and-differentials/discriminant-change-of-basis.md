# Discriminants under a change of basis

Let $B$ be a commutative algebra over a commutative ring $A$, let $\iota$ be a finite set, and for a family
$b = (b_i)_{i \in \iota}$ of elements of $B$ let

$$\operatorname{disc}_A(b) = \det \bigl( \operatorname{Tr}_{B/A}(b_i b_j) \bigr)_{i, j \in \iota},$$

where $\operatorname{Tr}_{B/A}(y)$ is the trace of multiplication by $y$ on $B$, taken to be $0$ if $B$ has no finite
basis over $A$. Then for every matrix $P = (P_{ij})_{i, j \in \iota}$ over $A$, the family $c$ with
$c_i = \sum_{j} P_{ij} b_j$ satisfies $\operatorname{disc}_A(c) = (\det P)^2 \operatorname{disc}_A(b)$.

## Sources

- F. Keune, *Number Fields*, Radboud University Press, Nijmegen (2023, version 2023-01), open access,
  <https://doi.org/10.54195/IPVU4488>, Proposition 1.27 ($\operatorname{disc}(\beta_1, \dots, \beta_n) = \det(T)^2 \operatorname{disc}(\alpha_1, \dots, \alpha_n)$
  for two bases of a finite field extension and the transition matrix $T$).
