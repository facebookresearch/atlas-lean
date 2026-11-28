# Time and space simulations for weak call-by-value decision problems

Let $\Sigma$ be a finite alphabet with $\{\mathsf{true}, \mathsf{false}\} \subseteq \Sigma$, let $f : \Sigma^* \to \{\mathsf{true}, \mathsf{false}\}$, and let $T, S \in \Omega(n)$. Use Scott encodings for strings, with the two Boolean outputs represented by fixed constant-size terms. Time is the number of β-steps and space is the size of the largest intermediate term, as in [the weak call-by-value λ-calculus and its time and space measures](weak-call-by-value-lambda-calculus-and-its-cost-measures.md).

1. If $f$ is computable by $\mathsf{L}$ in time $T$ and space $S$, then a multi-tape Turing machine computes $f$ in time $O(\mathrm{poly}(T(n)))$ and space $O(S(n))$.
2. If a deterministic single-tape Turing machine in the model of Dal Lago and Accattoli computes $f$ in time $T$ and space $S$, then $f$ is computable by $\mathsf{L}$ in time $O(\mathrm{poly}(T(n)))$ and space $O(S(n))$. This machine starts with the input on its tape and leaves the output on that tape in its final state.

The proof of the reverse simulation uses the single-tape model. Extending its hypothesis to arbitrary multi-tape machines requires a separate polynomial-time, linear-space model transfer, which is not asserted here. For general outputs the forward simulation yields a shared normal form; Boolean output has constant size, so the unfolding step preserves the stated bounds.

## Depends on

- [The weak call-by-value λ-calculus and its time and space measures](weak-call-by-value-lambda-calculus-and-its-cost-measures.md)

## Proof depends on

- [Turing machines are simulated by weak call-by-value terms with linear overhead](turing-machines-are-simulated-by-weak-call-by-value-terms-with-linear-overhead.md)
- [Weak call-by-value normal forms are computed in polynomial time as shared representations](shared-normal-forms-of-weak-call-by-value-terms-in-polynomial-time.md)

## Expansion

Before this node becomes ready, add or link:

- The function-computing machine models over a finite alphabet, with their input/output, time and space conventions: multi-tape in item 1 and the source's single-tape model in item 2 (statement prerequisites).
- The unfolding algorithm for a heap and closure, with its time and space bounds and the constant-size Boolean-output specialization (Forster, Kunze and Roth, Lemma 4.2 and the proof of Theorem 1.2 in Section 6 of the published version; Lemma 22 and Theorem 2 of arXiv:1902.07515v1; proof prerequisite).

The broader model-invariance target also needs a sourced transfer from the canonical multi-tape model to the source's single-tape model with polynomial time and linear space overhead. That is a separate model-scoping obligation, not a conclusion of this node.

## Sources

- Yannick Forster, Fabian Kunze and Marc Roth, "The Weak Call-by-Value λ-Calculus Is Reasonable for Both Time and Space", Proceedings of the ACM on Programming Languages 4 (POPL), Article 27, 2020: Theorem 1.2 and its proof in Section 6, using Theorem 4.3, Lemmas 4.1 and 4.2 and Theorem 5.1 (Theorem 2, Theorems 20, 21 and 23 and Lemma 22 of arXiv:1902.07515v1).
- Ugo Dal Lago and Beniamino Accattoli, "Encoding Turing Machines into the Deterministic Lambda-Calculus", arXiv:1711.10078, 2017: Section 5 and Theorem 5.5, for the single-tape model used in item 2; the published form of this encoding is Accattoli and Dal Lago, RTA 2012, LIPIcs 15, Theorem 6.1, stated for head reduction.
