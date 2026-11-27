# Göös et al.: PPAD^dt, PPADS^dt, SOPL^dt and EOPL^dt are characterized by uNS, uSA, RevRes and RevResT

For every unsatisfiable CNF formula $F$:

$$
\mathsf{PPAD}^{dt}(S(F))=\Theta(\mathrm{uNS}(F)),\qquad \mathsf{PPADS}^{dt}(S(F))=\Theta(\mathrm{uSA}(F)),
$$

$$
\mathsf{SOPL}^{dt}(S(F))=\Theta(\mathrm{RevRes}(F)),\qquad \mathsf{EOPL}^{dt}(S(F))=\Theta(\mathrm{RevResT}(F)).
$$

Quantitatively for PPAD: a degree-$d$, size-$L$ uNS refutation yields a depth-$O(d)$ END-OF-LINE formulation on $O(L)$ nodes, and a depth-$d$ END-OF-LINE formulation on $L$ nodes yields a uNS refutation of degree $O(d)$ and size $L2^{O(d)}$. In particular, polylogarithmic-width CNFs $F_n$ have uNS refutations of polylogarithmic degree and quasipolynomial size if and only if $S(F_n)\in\mathsf{PPAD}^{dt}$.

## Proof sketch

Formulation to proof: for each node $v$ let $S_v(x)\in\{-1,0,1\}$ be $+1$ if $v$ is a source other than the distinguished one, $-1$ if $v$ is a sink or the distinguished node fails to be a source, and $0$ otherwise; $S_v$ is a depth-$O(d)$ decision tree, so it is a signed sum of leaf indicator monomials, and $\sum_vS_v\equiv-1$, since a graph of in- and out-degree at most one has as many sources as sinks; negating rearranges this into $\sum_ip_i\overline{C_i}=1$ with unary integer coefficients. Proof to formulation: expand the identity into monomials with multiplicity, make one node per copy, and use two query-efficient matchings (cancellation inside each $p_i\overline{C_i}$ and across clauses) to orient a line structure whose unmatched ends are clause witnesses. For uSA the junta terms supply sources without sinks (SINK-OF-LINE), and the RevRes cases use a grid of proof lines with potential given by the step number.

## Depends on

- [Unary Nullstellensatz and unary Sherali–Adams refutations of CNF formulas](unary-nullstellensatz-and-unary-sherali-adams.md)
- [Reversible Resolution: a MaxSAT-style fragment of Resolution with consumed premises](reversible-resolution.md)
- [Query total search problems TFNP^dt, decision-tree formulations and the black-box classes](query-tfnp-and-formulations.md)
- [The false-clause search problem S(F) of an unsatisfiable CNF and its universality for TFNP^dt](false-clause-search-problem.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
