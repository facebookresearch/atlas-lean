# Separability of one-counter automata by definite or regular languages is undecidable

For any class $\mathcal{F}$ of languages that contains all definite languages, in particular for the regular languages, it is undecidable whether the languages of two given one-counter automata with zero tests can be separated by a member of $\mathcal{F}$.

**Definitions.** Languages $L, K \subseteq \Sigma^*$ are *separable* by a class $\mathcal{F}$ if there is $S \in \mathcal{F}$ with $L \subseteq S$ and $S \cap K = \emptyset$. The *$\mathcal{F}$-separability problem for languages of OCA* asks, given two [one-counter automata](one-counter-automata-and-one-counter-nets.md) $\mathcal{A}, \mathcal{B}$ over the same alphabet $\Sigma$, whether $L(\mathcal{A})$ and $L(\mathcal{B})$ are separable by $\mathcal{F}$. A language is *definite* if it is a finite Boolean combination of languages $w \Sigma^*$ with $w \in \Sigma^*$.

**Theorem.** For every language class $\mathcal{F}$ containing all definite languages, the $\mathcal{F}$-separability problem for languages of one-counter automata is undecidable. In particular, regular separability of one-counter automata is undecidable.

For one-counter nets, without zero tests, regular separability is decidable and $\mathbf{PSPACE}$-complete, and $\mathcal{F}$-separability is $\mathbf{PSPACE}$-hard for every class $\mathcal{F}$ containing the definite languages. Regularity of OCN languages does not reduce to their regular separability, since OCN languages are not closed under complement; indeed regularity is undecidable for OCN languages while regular separability is decidable.

## Depends on

- [One-counter automata and one-counter nets](one-counter-automata-and-one-counter-nets.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Space hierarchy theorem for space-constructible bounds](../../../hierarchy-theorems-and-barriers/space-hierarchy-theorem/space-hierarchy-theorem-for-space-constructible.md)

## Expansion

The argument follows Hunt's method: rather than reducing one fixed undecidable problem, it reduces in polynomial time every decidable problem to $\mathcal{F}$-separability of OCA. Every decidable set $L \subseteq \mathbb{N}$ is recognized by a total deterministic two-counter machine $\mathcal{M}$ that accepts or rejects with both counters zero. Given $k$, the reduction takes as alphabet the set of transitions of $\mathcal{M}$ and builds two OCA: $\mathcal{A}_1$ starts from $(q_0, k)$ and simulates $\mathcal{M}$ while tracking only the first counter, and $\mathcal{A}_2$ starts from $(q_0, 0)$ and tracks only the second, each using its zero tests for the tests of $\mathcal{M}$ on its counter and both ending in the accepting state with counter $0$. A word in both languages is an accepting computation of $\mathcal{M}$ on $k$, so if $k \in L$ the languages intersect and are not separable; if $k \notin L$ they are separable by a definite language. If $\mathcal{F}$-separability were decidable within some space bound $f$, every decidable problem would be decidable in space $f(p(n))$ for a polynomial $p$, contradicting the space hierarchy theorem.

## Sources

- W. Czerwiński and S. Lasota, "Regular separability of one counter automata", *Logical Methods in Computer Science* 15(2):20, 2019, doi:10.23638/LMCS-15(2:20)2019, <https://lmcs.episciences.org/4417>; numbering of arXiv:1701.02808v5: Theorem 2 in Section 1 (the undecidability theorem), proved in Section 7, Theorem 1 (regular separability of OCN is PSPACE-complete) and the PSPACE lower bound in Section 6.
