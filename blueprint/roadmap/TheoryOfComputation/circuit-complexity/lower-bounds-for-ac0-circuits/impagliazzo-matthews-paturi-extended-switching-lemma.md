# Impagliazzo–Matthews–Paturi extended switching lemma

Håstad's switching lemma extends to a whole sequence of $k$-CNFs and $k$-DNFs: after a random restriction leaving a $p\le 1/13$ fraction of the variables free, their common canonical decision tree has a path of length at least $s$ to which every formula contributes with probability at most $(13pk)^s$.

Let $\varphi_1,\dots,\varphi_m$ be a sequence of formulas in the same $n$ variables, each a $k$-CNF (every clause has at most $k$ literals) or a $k$-DNF (every term has at most $k$ literals). The canonical decision tree of a CNF is a leaf $0$ if some clause is empty and a leaf $1$ if no clause remains; otherwise it queries, in order, all variables of the first clause, restricts the formula by the answers (dropping satisfied clauses and falsified literals) and recurses. That of a DNF is defined dually. The canonical decision tree of the sequence $(\varphi_1,\dots,\varphi_m)$ builds the tree of $\varphi_1$ and, along each of its paths, restricts $\varphi_2,\dots,\varphi_m$ by the answers and recurses on the remaining sequence. The variables queried while a formula's tree is being built are the nodes that formula contributes to the path.

Let $p\le 1/13$ with $pn$ an integer, and let $\rho$ be a restriction chosen uniformly among all restrictions that leave exactly $pn$ variables unset and set each other variable to $0$ or $1$. Then for every natural number $s$:

1. the probability that the canonical decision tree of $(\varphi_1|_\rho,\dots,\varphi_m|_\rho)$ has a path of length at least $s$ to which every $\varphi_i$ contributes at least one node is at most $(13pk)^s$;
2. the probability that this tree has a path of length at least $s$ is at most $(2^m-1)(13pk)^s$.

## Expansion

The proof follows Beame's encoding proof of Razborov's version of the switching lemma. A restriction $\rho$ together with the first $s$ steps of a long path is encoded by a restriction leaving $s$ fewer variables unset, which sets each path variable so that its clause stays unsatisfied, plus, for each path variable, its index in its clause, a three-valued flag saying whether it is the last variable its formula contributes, the last its clause contributes, or neither, and its value on the path. Decoding recovers the clauses one by one, as the first clause not yet satisfied. Counting the encodings against the restrictions with $pn$ unset variables gives at most $\big(12pk/(1-p)\big)^s\le(13pk)^s$. Item 2 follows from item 1 by a union bound over the nonempty subsequences of formulas that contribute to the path, since a path of the tree of the sequence is a path of the tree of the subsequence of its contributing formulas.

## Depends on

- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)
- [Restriction of a CNF formula by a literal](../../../Logic/propositional-logic/conjunctive-normal-form/restrict-2.md)

## Proof depends on

None.

## Sources

- Russell Impagliazzo, William Matthews and Ramamohan Paturi, "A Satisfiability Algorithm for AC0", *Proceedings of the Twenty-Third Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2012)*, pp. 961–972, https://doi.org/10.1137/1.9781611973099.77, read in arXiv:1107.3127v1 <https://arxiv.org/abs/1107.3127v1> (Lemma 1.4, the Extended Switching Lemma, and Corollary 1.5; canonical decision trees of a sequence and contributed nodes in Section 2; the proof of Lemma 1.4 in Section 3.2, where $\rho$ is uniform over the restrictions with exactly $pn$ unset variables).
