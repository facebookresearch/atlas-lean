# Arteche–Atserias–de Rezende–Khaniki: a strong proof system is automatable iff it is automatable on Resolution lower bounds

For every reasonably strong proof system, and for Resolution itself, (weak) automatability is equivalent to (weak) automatability restricted to the tautologies $\neg\mathrm{Ref}_s(\varphi)$ stating Resolution lower bounds.

A proof system $S$ is **reasonably strong** if it is polynomially equivalent to $\mathrm{EF}+A$ for some polynomial-time recognizable set $A$ of tautologies. $S$ is **automatable on Ref formulas** if an algorithm, on inputs of the form $\neg\mathrm{Ref}_s(\varphi)$, outputs an $S$-proof in time polynomial in the size of the shortest one; weak automatability on Ref formulas is defined likewise with proofs in any system simulating $S$ on Ref formulas.

1. For every reasonably strong $S$: $S$ is automatable if and only if $S$ is automatable on Ref formulas.
2. For every reasonably strong $S$: $S$ is weakly automatable if and only if $S$ is weakly automatable on Ref formulas.
3. Resolution is automatable if and only if it is automatable on Ref formulas, and weakly automatable if and only if it is weakly automatable on Ref formulas.

Thus proof search in arbitrarily strong systems is characterized by proof search for Resolution lower bounds.

## Expansion

If $S$ refutes an unsatisfiable $\varphi$ in size $t$, then by the formalized correctness of the assignment-extraction algorithm $S$ refutes $\mathrm{Ref}_{p(n,m)}(\mathrm{Ref}_{n^{3}}(\varphi))$ in size $\mathrm{poly}(n,m,t)$ for a fixed polynomial $p$, and conversely such a refutation converts efficiently back into a refutation of $\varphi$. So an automating algorithm for Ref formulas, run on $\mathrm{Ref}_{p(n,m)}(\mathrm{Ref}_{n^{3}}(\varphi))$, automates $S$ on all inputs. This needs $S$ to prove the extraction algorithm correct, hence $S\ge\mathrm{EF}$; for Resolution the semantics of Ref compensates. The same circle of ideas gives explicit Ref formulas exponentially hard for bounded-depth Frege, and for every consistent polynomial-time axiomatized theory $T$ extending $S^1_2$ with $\mathbb N$ as a model, explicit unsatisfiable formulas exponentially hard for Resolution for which $T$ cannot prove even an $N^{c}$ Resolution lower bound.

## Depends on

- [The Proof Analysis Problem PAP and analyzable proof systems](proof-analysis-problem.md)
- [Automatable proof systems](../../../../Logic/proof-theory/automatability-of-proof-systems/automatable-proof-system.md)

## Proof depends on

- [Arteche–Atserias–de Rezende–Khaniki: short Resolution proofs of Resolution lower bounds leak satisfying assignments](resolution-proof-analysis-is-in-fp.md)
- [The Atserias–Müller reduction from SAT to resolution proof size](../../../../Logic/proof-theory/automatability-of-proof-systems/am-reduction-formula.md)

## Sources

- Noel Arteche, Albert Atserias, Susanna F. de Rezende and Erfan Khaniki, "The Proof Analysis Problem", *66th IEEE Symposium on Foundations of Computer Science (FOCS 2025)*, 2025, https://doi.org/10.1109/FOCS63196.2025.00133; numbering from arXiv:2506.16956v2 (Theorem 1.9, Definition 9.1, Proposition 9.2, Theorems 9.5, 9.6, 9.7 and 9.8, Theorem 9.10, Theorem 9.13).
