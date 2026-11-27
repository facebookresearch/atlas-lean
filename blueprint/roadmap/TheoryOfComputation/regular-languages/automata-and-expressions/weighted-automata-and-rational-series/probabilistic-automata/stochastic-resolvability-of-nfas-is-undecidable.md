# Stochastic resolvability of NFAs is undecidable

No algorithm decides whether the nondeterminism of a given finite automaton can be resolved by a memoryless randomized choice of transitions so that every word of its language is accepted with probability at least $\lambda$; this holds already for $\lambda = 1/4$.

**Stochastic resolvers.** Let $\mathcal{A}$ be a nondeterministic finite automaton with state set $Q$, alphabet $\Sigma$ and transition set $\Delta$. A (memoryless) *stochastic resolver* for $\mathcal{A}$ is a map $\mathcal{R} \colon \Delta \to [0, 1]$ such that $\sum_{q} \mathcal{R}(p, \sigma, q) = 1$ for every state $p$ and letter $\sigma$. It turns $\mathcal{A}$ into a probabilistic automaton $\mathcal{P}^{\mathcal{A}}_{\mathcal{R}}$ on the same states, which accepts each word with some probability; for a threshold $\lambda$, let $L(\mathcal{P}_{\ge \lambda})$ be the set of words accepted with probability at least $\lambda$. Since every run with positive probability is a run of $\mathcal{A}$, $L(\mathcal{P}_{\ge \lambda}) \subseteq L(\mathcal{A})$ for $\lambda > 0$. The automaton $\mathcal{A}$ is *$\lambda$-resolvable* (memoryless stochastically resolvable with threshold $\lambda$) if some resolver gives $L(\mathcal{P}_{\ge \lambda}) = L(\mathcal{A})$.

**Theorem (Paul, Purser, Schewe, Tang, Totzke and Yen).** The *$\lambda$-resolvability problem* for NFAs, which asks whether a given NFA is $\lambda$-resolvable, is undecidable; the reduction uses the fixed threshold $\lambda = 1/4$.

The problem is decidable for finitely ambiguous automata, and the undecidability carries over to automata on infinite words, as the source shows. For $\lambda = 1$ resolvability coincides with history-determinism on finite words.

## Depends on

- [Probabilistic automata and cut-point languages](../probabilistic-automata-and-cut-point-languages.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../emptiness-problem-for-probabilistic-automata.md)

## Expansion

A probabilistic automaton is *simple* if all its transition probabilities lie in $\{0, \frac12, 1\}$; its probabilities are then determined by its underlying NFA. Strict emptiness of simple probabilistic automata with cut-point $\frac12$ is undecidable (Gimbert and Oualhadj, as the source recalls), so by complementing the accepting states it is undecidable whether a simple probabilistic automaton $\mathcal{P}$ accepts every word with probability at least $\frac12$ (Lemma 3.3 of the source). From the underlying NFA $\mathcal{A}$ of $\mathcal{P}$ one builds a larger NFA $\mathcal{A}'$ whose only possible $\frac14$-resolver reproduces the probabilities of $\mathcal{P}$ on the copy of $\mathcal{A}$; then $\mathcal{A}'$ is $\frac14$-resolvable if and only if $\mathcal{P}$ accepts every word with probability at least $\frac12$.

## Sources

- S. Paul, D. Purser, S. Schewe, Q. Tang, P. Totzke and D.-D. Yen, "Resolving Nondeterminism by Chance", in *36th International Conference on Concurrency Theory (CONCUR 2025)*, Leibniz International Proceedings in Informatics (LIPIcs) 348, 2025, paper 32, doi:10.4230/LIPIcs.CONCUR.2025.32; read as arXiv:2504.10234v2, <https://arxiv.org/abs/2504.10234v2>: Theorem 3.2 (the $\lambda$-resolvability problem is undecidable for NFAs) with its proof and Lemma 3.3, the definitions of stochastic resolvers and $\lambda$-resolvability in Section 2, and the abstract and introduction (finitely ambiguous automata, infinite words, $\lambda = 1$), in the numbering of that version.
