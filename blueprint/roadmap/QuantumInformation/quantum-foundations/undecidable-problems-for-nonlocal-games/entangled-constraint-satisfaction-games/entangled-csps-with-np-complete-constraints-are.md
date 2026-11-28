# Entangled constraint satisfaction problems without a weak near-unanimity polymorphism are RE-complete in the non-TVF, Boolean and 3-coloring cases


For every constraint language on the hard side of the CSP dichotomy (no weak near-unanimity polymorphism, which makes its classical satisfiability problem NP-complete) that is not two-variable falsifiable, or is Boolean, or is 3-coloring, the succinct entangled gap problem with perfect completeness and some constant soundness is RE-complete; the explicit version is undecidable.

**Theorem (Culf and Mastel).** Let $\Gamma$ be a set of constraints over $\mathbb Z_k$, in the sense of [constraint system games and entangled CSPs](constraint-system-games-and-entangled-csps.md), and let $\mathbb A_\Gamma$ be the [finite template](../../../../TheoryOfComputation/np-completeness/satisfiability/finite-domain-csp-dichotomy/finite-templates-and-csp-of-a.md) on $\mathbb Z_k$ with one relation $C \subseteq \mathbb Z_k^{V}$ for each constraint $(V, C) \in \Gamma$, the variables of $V$ taken in a fixed order, so that $\mathrm{CSP}(\Gamma)_{1,1}$ is $\mathrm{CSP}(\mathbb A_\Gamma)$. Suppose that $\mathbb A_\Gamma$ has no [weak near-unanimity](../../../../TheoryOfComputation/np-completeness/satisfiability/finite-domain-csp-dichotomy/wnu-taylor-siggers-cyclic-operations.md) [polymorphism](../../../../TheoryOfComputation/np-completeness/satisfiability/finite-domain-csp-dichotomy/polymorphism-clone-of-a-finite-structure.md); for Boolean $\Gamma$ this says that none of the constant maps $0$ and $1$, $\wedge$, $\vee$, majority and minority preserves every constraint of $\Gamma$ (Theorems 4.7 and 4.10 of the source). This makes $\mathrm{CSP}(\Gamma)_{1,1}$ NP-complete, and it is equivalent to NP-completeness if $\mathsf P \ne \mathsf{NP}$. Suppose moreover that one of the following holds:

1. $\Gamma$ is not TVF;
2. $\Gamma$ is Boolean ($k = 2$);
3. $\Gamma = \{\neq_{\mathbb Z_3}\}$ is 3-coloring.

Then there is a constant $s \in [0, 1)$ such that $\mathrm{SuccinctCSP}_{c\text{-}v}(\Gamma)^*_{1,s}$ is RE-complete (Theorem 4.14 of the source), and the same holds for $\mathrm{SuccinctCSP}_{c\text{-}c}(\Gamma)^*_{1,s}$ (Corollary 4.15). Moreover, for such $\Gamma$ there is a constant $s \in [0, 1)$ such that $\mathrm{CSP}_{c\text{-}v}(\Gamma)^*_{1,s}$ and $\mathrm{CSP}_{c\text{-}c}(\Gamma)^*_{1,s}$ are RE-complete with respect to exponential-time reductions (Corollary 4.18); in particular these explicit problems are undecidable.

The source states the theorem with the hypothesis that $\mathrm{CSP}(\Gamma)_{1,1}$ is NP-complete; its proofs use that hypothesis through the hardness side of the dichotomy, the constraint-by-constraint reductions in the proof of Corollary 4.8 and the absence of the majority polymorphism in the proof of Theorem 7.29, which is what the hypothesis above provides. RE-hardness is witnessed by a polynomial-time map from instances of the halting problem to instances of the succinct problem preserving yes and no instances. The source leaves open whether non-Boolean TVF constraint languages other than 3-coloring, such as $k$-coloring for $k \geq 4$, are RE-complete in this sense. Call a constraint $(V, C)$ *empty* if $C = \Sigma^V$, so that it accepts every assignment (Definition 6.1 of the source). An empty constraint on two or more variables is not TVF, so a language satisfying the hardness hypothesis above that contains one falls under case 1.

## Depends on

- [Constraint system games and entangled constraint satisfaction problems](constraint-system-games-and-entangled-csps.md)
- [Finite relational templates and the homomorphism problem CSP(A)](../../../../TheoryOfComputation/np-completeness/satisfiability/finite-domain-csp-dichotomy/finite-templates-and-csp-of-a.md)
- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](../../../../TheoryOfComputation/np-completeness/satisfiability/finite-domain-csp-dichotomy/polymorphism-clone-of-a-finite-structure.md)
- [Weak near-unanimity, Taylor, Siggers and cyclic operations on a finite set](../../../../TheoryOfComputation/np-completeness/satisfiability/finite-domain-csp-dichotomy/wnu-taylor-siggers-cyclic-operations.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Polynomial-time reduction between promise problems](../../../../TheoryOfComputation/randomized-and-quantum-complexity/local-hamiltonian-problem/promise-reduces.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem reduces to the entangled value gap problem](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/halting-problem-reduces-to-entangled-value-gap.md)
- [MIP* is contained in RE](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/mip-star-is-contained-in-re.md)
- [Bulatov and Zhuk: the CSP dichotomy theorem for finite templates](../../../../TheoryOfComputation/np-completeness/satisfiability/finite-domain-csp-dichotomy/bulatov-zhuk-csp-dichotomy-theorem.md)

## Expansion

The proof starts from the output of the proof of $\mathrm{MIP}^* = \mathrm{RE}$ in the refinement of Dong, Fu, Natarajan, Qin, Xu and Yao, in which the RE-hard games are synchronous Boolean constraint system games with polynomial-length questions and constant-length answers, whose perfect strategies can be taken oracularizable. The classical reduction from such a Boolean constraint system to a system in $\mathrm{CSP}(\Gamma)$ is then shown to be sound against entangled players: strategies correspond to tracial states on weighted constraint system algebras, and reductions are $*$-homomorphisms between these algebras that change the defect by at most a constant factor. An improved context subdivision transformation keeps the soundness constant without parallel repetition, provided every pair of variables shares a constraint; for this, commutativity gadgets replace empty constraints: one-constraint gadgets for non-TVF languages, a triangular gadget built from copies of 1-in-3-SAT for Boolean TVF languages, and a prism gadget of Ji for 3-coloring. Membership in RE follows from $\mathrm{MIP}^* \subseteq \mathrm{RE}$. A good expansion links the refinement of $\mathrm{MIP}^* = \mathrm{RE}$ to constant-length answers, the equivalence of synchronous oracularizable games with Boolean constraint system games and the synchronous rounding theorem of de la Salle and Marrakchi, besides the CSP dichotomy theorem linked above.

## Sources

- E. Culf and K. Mastel, "RE-completeness of entangled constraint satisfaction problems", in *2025 IEEE 66th Annual Symposium on Foundations of Computer Science (FOCS 2025)*, IEEE, 2025, pp. 2194–2230, doi:10.1109/FOCS63196.2025.00116; read as arXiv:2410.21223v2, <https://arxiv.org/abs/2410.21223v2>: Section 1, Section 4 (Theorems 4.7 and 4.10, Corollary 4.8 with its proof sketch, Theorem 4.14, Corollaries 4.15 and 4.18 and the discussion after them), Definition 6.1, Theorem 7.29 and the proofs in Sections 5 to 9.
