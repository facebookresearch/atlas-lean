# Satisfiability in the projector algebras of all finite-dimensional or all Hilbert spaces is undecidable

No algorithm decides whether a propositional formula can be satisfied by projectors on some finite-dimensional Hilbert space, or on some Hilbert space, with connectives applied only to commuting projectors; this holds over the reals and over the complex numbers.

**Theorem (Dawar and Shah).** For $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$, the problems [$\mathbf{SAT}(\mathbf{P}(\mathbb{K}^{<\omega}))$ and $\mathbf{SAT}(\mathbf{P}(\mathbb{K}^\infty))$](satisfiability-in-projector-partial-algebras.md) are undecidable (Theorem 7.4 of the source). The source adds that $\mathbf{SAT}(\mathbf{P}(\mathbb{K}^{<\omega}))$ is complete for the class of recursively enumerable languages.

By contrast, the source shows that satisfiability in the class of all non-trivial partial Boolean algebras is NP-complete, and that for each fixed dimension $d \ge 3$ over $\mathbb{R}$ and $d \ge 4$ over $\mathbb{C}$ satisfiability in $\mathbf{P}(\mathbb{K}^d)$ is complete for the existential theory of the reals.

## Depends on

- [Satisfiability in partial Boolean algebras of projectors](satisfiability-in-projector-partial-algebras.md)

## Proof depends on

- [Quantum commuting isomorphism of graphs is undecidable](../undecidable-problems-for-nonlocal-games/nonlocal-games-on-graphs/quantum-commuting-isomorphism-is-undecidable.md)

## Expansion

For finite relational structures $\mathcal{M}$ and $\mathcal{N}$ and a Hilbert space $\mathcal{H}$, an $\mathcal{H}$-quantum homomorphism is a family of projectors $F_{m,n}$ with $\sum_n F_{m,n} = I$ for each $m$, with $F_{m,n}$ and $F_{m',n'}$ commuting whenever $m, m'$ occur in a common tuple, and with products over a tuple of $\mathcal{M}$ mapped outside the relation of $\mathcal{N}$ equal to $0$ (Definition 7.1 of the source). Proposition 7.3 of the source computably reduces the existence of an $\mathcal{H}$-quantum homomorphism to satisfiability in $\mathbf{P}(\mathcal{H})$, preserving the Hilbert space. The existence of quantum homomorphisms over all finite-dimensional, or over all, $\mathbb{K}$-Hilbert spaces is undecidable by results of Atserias, Kolaitis and Severini on operator assignments for constraint satisfaction problems and of Atserias, Mančinska, Roberson, Šámal, Severini and Varvitsiotis on quantum graph isomorphism, which the source cites. A complete expansion links the undecidability of operator solutions of Boolean constraint satisfaction problems (Atserias, Kolaitis and Severini, *Journal of Computer and System Sciences* 105:171–198, 2019), which has no page here.

## Sources

- Anuj Dawar and Nihil Shah, "Complexity of satisfiability in Kochen–Specker partial Boolean algebras", in *41st Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2026)*, LIPIcs 380, 37:1–37:25, 2026, doi:[10.4230/LIPIcs.LICS.2026.37](https://doi.org/10.4230/LIPIcs.LICS.2026.37). Numbering of the version read, arXiv:2602.24164v1: Theorem 7.4 and the remark after it, Definition 7.1 and Proposition 7.3.
