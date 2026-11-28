# Whether a context-free language is a chain, or has exponential antichain growth, is undecidable

For context-free grammars over a partially ordered alphabet it is undecidable whether all generated words are pairwise comparable in the lexicographic order, and also whether the language has exponential antichain growth.

**Theorem.** Order words [lexicographically](antichain-growth-of-a-language.md) by a partial order on their alphabet. There is no algorithm that decides, given a finite partially ordered alphabet $\Sigma$ and a context-free grammar $G$ over $\Sigma$, whether $L(G)$ is a chain (the problem CFG-Chain). There is no algorithm that decides, given such $\Sigma$ and $G$, whether $L(G)$ has exponential antichain growth (the problem CFG-ExpAntichain).

For [regular languages](../../regular-languages/automata-and-expressions/kleene-s-theorem/is-regular-iff-exists-regex.md), given by NFAs, exponential antichain growth is decidable in [polynomial time](../../complexity-classes/the-classes-p-np-and-conp/p.md) (Theorem 18 of the source). Every context-free language has either polynomial or exponential antichain growth (Theorem 34), so the second problem is also that of deciding which of the two cases holds.

## Depends on

- [Antichain growth of a language](antichain-growth-of-a-language.md)
- [Partially ordered set](../../../Order/ordered-sets/partial-order.md)
- [Context-free languages](../grammars-and-pushdown-automata/context-free-languages.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Whether two context-free languages intersect is undecidable](../../undecidable-problems/undecidable-problems-for-context-free-grammars/exists-not-tm2-decidable-overlap.md)
- [PCP many-one reduces to nonemptiness of the intersection of two context-free languages](../../undecidable-problems/intersection-problem-for-context-free-languages/many-one-reducible-pcp-inter.md)

## Expansion

The proof starts from the undecidability of nonemptiness of $L(G_1) \cap L(G_2)$ for context-free grammars (Lemma 36). Extend $\Sigma$ by two letters $0, 1$, put an arbitrary linear order on $\Sigma$, and place every letter of $\Sigma$ below both $0$ and $1$, with $0$ and $1$ incomparable. A grammar $\widetilde G$ with $L(\widetilde G) = L(G_1)0 \cup L(G_2)1$ generates a chain iff $L(G_1) \cap L(G_2) = \emptyset$, since two words $u0$ and $v1$ are incomparable exactly when $u = v$ (Lemma 37). Next, extend $\Sigma$ by a letter $0$ above every letter and let $L(\widetilde G) = (L(G)0)^*$: if $L(G)$ is a chain, then $L(G)0$ is a prefix-free chain and its star is a chain (Lemma 38); if $l_1, l_2 \in L(G)$ are incomparable, then $(l_10 + l_20)^* \subseteq L(\widetilde G)$ contains an exponential antichain. So $L(\widetilde G)$ has exponential antichain growth iff $L(G)$ is not a chain (Lemma 39). A good expansion links the prefixing and concatenation lemmas for the lexicographic order (Lemmas 3 and 5 of the source), which Lemma 38 uses.

## Sources

- D. Mestel, "Widths of Regular and Context-Free Languages", in *39th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2019)*, Leibniz International Proceedings in Informatics 150, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2019, article 49, doi:[10.4230/LIPIcs.FSTTCS.2019.49](https://doi.org/10.4230/LIPIcs.FSTTCS.2019.49); read as arXiv:1709.08696v5, whose numbering is used here: Definition 35, Lemmas 36 to 39, Theorem 40, Theorem 18 and Theorem 34.
