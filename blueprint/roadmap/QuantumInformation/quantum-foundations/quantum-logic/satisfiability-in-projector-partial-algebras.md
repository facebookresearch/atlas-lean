# Satisfiability in partial Boolean algebras of projectors

The projectors on a real or complex Hilbert space form a partial Boolean algebra in which $\wedge$ and $\vee$ are defined only on commuting projectors; a propositional formula is satisfiable in it when some assignment of projectors makes every connective defined and the value nonzero.

**Partial Boolean algebras.** A *partial Boolean algebra* $A$ is a set with elements $0_A, 1_A$, a reflexive symmetric relation $\odot_A$ (*commeasurability*), a function $\neg_A : A \to A$ and functions $\vee_A, \wedge_A : \odot_A \to A$, such that every set $S$ of pairwise commeasurable elements is contained in a set $T \supseteq S \cup \{0_A, 1_A\}$ of pairwise commeasurable elements on which the operations form a [Boolean algebra](../../../Order/lattices-boolean-algebras/boolean-algebra.md).

**Projector algebras.** For a real or complex Hilbert space $\mathcal{H}$, $\mathbf{P}(\mathcal{H})$ is the set of [orthogonal projections](../gleason-s-theorem/is-orth-proj.md) on $\mathcal{H}$ with $1 = I$, $0 = 0$, $E \odot F$ iff $EF = FE$, $\neg E = I - E$, $E \vee F = E + F - EF$ and $E \wedge F = EF$. For $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$, $\mathbf{P}(\mathbb{K}^{<\omega}) = \{\mathbf{P}(\mathbb{K}^d) : d \in \mathbb{N}\}$ is the class of projector algebras of finite-dimensional $\mathbb{K}$-Hilbert spaces and $\mathbf{P}(\mathbb{K}^\infty)$ the class of projector algebras of all $\mathbb{K}$-Hilbert spaces.

**Meaningful substitution.** Propositional formulas are built from variables and $\top$ with $\neg$, $\vee$, $\wedge$. For a formula $\phi(p_1, \dots, p_n)$ and a partial Boolean algebra $A$, the *meaningful domain* $D_\phi \subseteq A^n$ and the value $\phi^A$ on it are defined by recursion: $\top$ and variables are defined everywhere, with values $1_A$ and the assigned element; $\neg\psi$ has the domain of $\psi$ and value $\neg_A \psi^A$; and $\psi_1 \bowtie \psi_2$, for $\bowtie \in \{\vee, \wedge\}$, is defined at an assignment $\alpha$ in both domains exactly when $\psi_1^A(\alpha) \odot_A \psi_2^A(\alpha)$, with value $\psi_1^A(\alpha) \bowtie_A \psi_2^A(\alpha)$.

**Satisfiability.** $\phi$ is *weakly satisfied* in $A$ if $\phi^A(\alpha) \ne 0_A$ for some $\alpha \in D_\phi$, and *strongly satisfied* if $\phi^A(\alpha) = 1_A$ for some $\alpha \in D_\phi$. For a class $\mathcal{C}$ of partial Boolean algebras, $\phi$ is $\mathcal{C}$-weakly (strongly) satisfiable if it is weakly (strongly) satisfied in some member of $\mathcal{C}$. When the two notions coincide on $\mathcal{C}$, the decision problem is written $\mathbf{SAT}(\mathcal{C})$; the source uses this notation for $\mathbf{P}(\mathbb{K}^{<\omega})$ and $\mathbf{P}(\mathbb{K}^\infty)$. The input is a propositional formula.

## Depends on

- [Boolean algebra](../../../Order/lattices-boolean-algebras/boolean-algebra.md)
- [Orthogonal projection](../gleason-s-theorem/is-orth-proj.md)

## Proof depends on

None.

## Sources

- Anuj Dawar and Nihil Shah, "Complexity of satisfiability in Kochen–Specker partial Boolean algebras", in *41st Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2026)*, LIPIcs 380, 37:1–37:25, 2026, doi:[10.4230/LIPIcs.LICS.2026.37](https://doi.org/10.4230/LIPIcs.LICS.2026.37). Numbering of the version read, arXiv:2602.24164v1: Definition 2.1 (partial Boolean algebras), Definition 2.4 (meaningful substitution), Section 3 (weak and strong satisfiability; Proposition 3.3), Definition 5.1 (projector algebras) and the notation of Section 7.
