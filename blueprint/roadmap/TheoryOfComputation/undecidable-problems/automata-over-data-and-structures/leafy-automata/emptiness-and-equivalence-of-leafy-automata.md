# Emptiness of level-2 leafy automata and equivalence of level-1 leafy automata are undecidable

Leafy automata read words of tags paired with data values from an infinitely branching forest and keep a finite labeled subtree of data values; emptiness is undecidable from level $2$ on, and equivalence of accepted languages is undecidable already at level $1$, where emptiness is decidable.

**Data values.** Let $\mathcal{D}$ be a countably infinite set with a parent function $\mathit{pred} \colon \mathcal{D} \to \mathcal{D} \cup \{\bot\}$ such that every $d \in \mathcal{D} \cup \{\bot\}$ has infinitely many children and every $d$ has a *level* $i$ with $\mathit{pred}^{i+1}(d) = \bot$.

**Leafy automata.** A *level-$k$ leafy automaton* $(\Sigma, k, Q, \delta)$ has a finite alphabet $\Sigma = \Sigma_{\mathsf{Q}} + \Sigma_{\mathsf{A}}$ of questions and answers, finite sets $Q^{(0)}, \dots, Q^{(k)}$ of level-$i$ states, and finite transition relations $\delta^{(i)}_{\mathsf{Q}} \subseteq Q^{(0)} \times \dots \times Q^{(i-1)} \times \Sigma_{\mathsf{Q}} \times Q^{(0)} \times \dots \times Q^{(i)}$ and $\delta^{(i)}_{\mathsf{A}} \subseteq Q^{(0)} \times \dots \times Q^{(i)} \times \Sigma_{\mathsf{A}} \times Q^{(0)} \times \dots \times Q^{(i-1)}$ for $0 \le i \le k$. A configuration $(D, E, f)$ consists of the finite set $D$ of data values read so far, a finite rooted subtree $E$ of $\mathcal{D}$ and a level-preserving labeling $f \colon E \to Q$; the initial configuration is empty. Reading $(t, d)$ with $t$ a question and $d$ a fresh level-$i$ value whose parent is in $E$ adds $d$ as a leaf and updates the states on the branch from the root to $d$ according to $\delta^{(i)}_{\mathsf{Q}}$; reading $(t, d)$ with $t$ an answer and $d$ a leaf of $E$ of level $i$ deletes $d$ and updates the states on its branch according to $\delta^{(i)}_{\mathsf{A}}$. A word over $\Sigma \times \mathcal{D}$ is *accepted* if a nonempty sequence of such steps reads it from the empty configuration and ends with $E$ empty; $L(\mathcal{A})$ is the set of accepted words.

**Theorem (Dixon, Lazić, Murawski and Walukiewicz).**

1. The emptiness problem for level-$2$ leafy automata is undecidable.
2. The equivalence problem for level-$1$ leafy automata, which asks whether $L(\mathcal{A}_1) = L(\mathcal{A}_2)$, is undecidable.

For level-$1$ leafy automata, emptiness is interreducible with reachability in vector addition systems with states, so it is decidable but not elementary.

## Depends on

None.

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Both items reduce the halting problem for two-counter machines, undecidable because such machines simulate Turing machines. For item 1, the root holds the state of the machine, two level-$1$ nodes stand for the counters, and the number of level-$2$ children of a counter node is its value; a zero test removes the counter node and creates a new one, which is possible only when it has no children. For item 2, one level-$1$ automaton accepts the encodings of pseudo-runs of a deterministic machine started and ended with zero counters, with matched increments and decrements, and a second accepts those that in addition contain an incorrect zero test; the two languages are equal exactly when the machine does not halt.

## Sources

- A. Dixon, R. Lazić, A. S. Murawski and I. Walukiewicz, "Leafy automata for higher-order concurrency", in *Foundations of Software Science and Computation Structures (FoSSaCS 2021)*, Lecture Notes in Computer Science 12650, Springer, 2021, pp. 184–204, doi:10.1007/978-3-030-71995-1_10; read as arXiv:2101.08720v1, <https://arxiv.org/abs/2101.08720v1>: Lemma 1 (emptiness for level $2$, and the level-$1$ comparison with vector addition systems) and Lemma 2 (equivalence for level $1$) with the proof in the appendix, and the definitions of data values, leafy automata, configurations, transitions and accepted traces in the section on leafy automata, in the numbering of that version.
