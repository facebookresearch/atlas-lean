# Reachability properties of quantum automata are undecidable

For finite-dimensional quantum automata with rational data, no algorithm decides whether every path eventually reaches, always stays in, ultimately stays in, or infinitely often visits a set of states described by a Boolean combination of subspaces, once the description may use negation.

**Quantum automata.** A *quantum automaton* $\mathcal{A} = (\mathcal{H}, \mathit{Act}, \{U_\alpha\}_{\alpha \in \mathit{Act}}, \mathcal{H}_{\mathrm{ini}})$ has a finite-dimensional Hilbert space $\mathcal{H}$, a finite set $\mathit{Act}$ of actions, a unitary operator $U_\alpha$ on $\mathcal{H}$ for each action, and a subspace $\mathcal{H}_{\mathrm{ini}}$ of initial states. A *path* is a sequence $\psi_0, \psi_1, \psi_2, \dots$ of states with $\psi_0 \in \mathcal{H}_{\mathrm{ini}}$, $\lVert \psi_0 \rVert = 1$ (states are unit vectors, as the measurement probabilities of Section 2.1 of the source require; unitarity keeps every $\psi_n$ a unit vector) and $\psi_{n+1} = U_{\alpha_n} \psi_n$ for some infinite action sequence $\alpha_0 \alpha_1 \cdots$. Atomic propositions are subspaces of $\mathcal{H}$, a state $\psi$ satisfying the subspace $V$ when $\psi \in V$; formulas $f$ are built from subspaces with the classical connectives $\neg$, $\wedge$, $\vee$ (Boolean, not the lattice operations of quantum logic). For an infinite sequence of states, $\mathbf{F} f$ holds if some state satisfies $f$, $\mathbf{G} f$ if every state does, $\mathbf{U} f$ (ultimately forever) if all states from some index on do, and $\mathbf{I} f$ (infinitely often) if infinitely many do. $\mathcal{A} \models \Delta f$ if the state sequence of every path satisfies $\Delta f$.

**Inputs.** Subspaces are identified with their [orthogonal projections](../../../../QuantumInformation/quantum-foundations/gleason-s-theorem/is-orth-proj.md); all unitary and projection operators are given as matrices in a fixed orthonormal basis whose entries are rational complex numbers (the source assumes that all complex numbers in the input are rational).

**Theorem (Li and Ying).** For each $\Delta \in \{\mathbf{F}, \mathbf{G}, \mathbf{U}, \mathbf{I}\}$, it is undecidable whether $\mathcal{A} \models \Delta f$ for a given quantum automaton $\mathcal{A}$ and formula $f$ (Theorem 2.1 of the source).

The source shows undecidability already for formulas of a simple form containing one negation. In contrast, for $\Delta \in \{\mathbf{G}, \mathbf{U}, \mathbf{I}\}$ the problem becomes decidable when $f$ contains no negation (Theorem 2.2 of the same paper).

## Depends on

- [Orthogonal projection](../../../../QuantumInformation/quantum-foundations/gleason-s-theorem/is-orth-proj.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [The Post correspondence problem is undecidable](../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

With a one-dimensional initial subspace, $\mathcal{A} \models \mathbf{G} f$ iff the language of action words $s$ with $U_s \psi_0 \models \neg f$ is empty, and $\mathbf{U}$ and $\mathbf{I}$ reduce to finiteness and liveness conditions on such languages. For $\mathbf{G}$, $\mathbf{U}$ and $\mathbf{I}$ the paper reduces the undecidable question whether some product of given matrices sends a fixed vector into a fixed hyperplane $V$, that is, whether $u^{T} M v = 0$ for some product $M$ (so $\mathcal{A} \models \mathbf{G}\, \neg V$ holds exactly when no such product exists; Theorem 3.3 of the source and the paragraph after it), an emptiness problem for quantum automata that the source cites as a theorem of Blondel, Jeandel, Koiran and Portier (the general matrix version is due to Paz and to Cassaigne and Karhumäki, by reduction from the Post correspondence problem), with a silent action added for $\mathbf{U}$ and $\mathbf{I}$. For $\mathbf{F}$ it encodes the halting problem for two-counter machines: a counter value $n$ is stored as $G^n|0\rangle$ for a qubit unitary $G$ of infinite order (an eigenvalue $(3+4i)/5$), instruction labels as basis states, and two subspaces $V, W$ are chosen so that every path other than the simulation satisfies $\mathbf{F}(V \wedge \neg W)$, while the simulation does exactly when the machine halts. A complete expansion links that matrix-semigroup emptiness theorem.

## Sources

- Y. Li and M. Ying, "(Un)decidable problems about reachability of quantum systems", in *CONCUR 2014: Concurrency Theory*, Lecture Notes in Computer Science, Springer, 2014, pp. 482–496, doi:10.1007/978-3-662-44584-6_33; read in arXiv:1401.6249v1: the definitions of quantum automata and reachability properties, the input convention and Theorems 2.1 and 2.2 of the section "Main Theorems", and its proofs in the following sections.
