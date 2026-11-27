# Automatic structure

An automatic structure is a relational structure whose domain is a regular set of words and whose relations are recognized by synchronous multi-tape finite automata; the automata form a finite presentation of the structure.

**Definition.** Let $\Sigma$ be a finite alphabet and $\Sigma_\diamond = \Sigma \cup \{\diamond\}$ with a padding symbol $\diamond \notin \Sigma$. The *convolution* of words $w_1, \dots, w_n \in \Sigma^*$ is the word $w_1 \otimes \cdots \otimes w_n$ over $(\Sigma_\diamond)^n$ of length $\max_i |w_i|$ whose $k$-th letter is $(\sigma_1, \dots, \sigma_n)$, where $\sigma_i$ is the $k$-th letter of $w_i$ if $k \le |w_i|$ and $\diamond$ otherwise. An $n$-ary relation $R$ on $\Sigma^*$ is *FA recognizable* if the set of convolutions of the tuples in $R$ is a regular language. A relational structure with countable domain is *automatic over $\Sigma$* if its domain is a regular subset of $\Sigma^*$ and each of its relations is FA recognizable. A tuple $P$ of finite automata accepting the domain and the relations is an *automatic presentation* of the structure $S(P)$ it defines; a structure isomorphic to some $S(P)$ is *automatically presentable*. For a class $\mathcal C$ of structures, the *isomorphism problem* asks, given automatic presentations $P_1, P_2$ of structures in $\mathcal C$, whether $S(P_1) \cong S(P_2)$.

For example $(\mathbb N; \le, +)$ and $(\mathbb Q; \le)$ are automatically presentable, while $(\mathbb N; \times)$ and $(\mathbb Q; +)$ are not.

## Depends on

- [Kleene's theorem](../../../regular-languages/automata-and-expressions/kleene-s-theorem/is-regular-iff-exists-regex.md)

## Proof depends on

None.

## Expansion

The theory of an automatic structure in first-order logic extended with the quantifiers "there exist infinitely many" and "there exist finitely many, a number congruent to $n$ modulo $m$" is decidable, uniformly in the presentation, and every relation definable in that logic is again FA recognizable (Theorem 1 of the source). The isomorphism problem is the natural question this leaves open: deciding whether two presentations describe the same structure.

## Sources

- D. Kuske, J. Liu and M. Lohrey, "The Isomorphism Problem on Classes of Automatic Structures", in *Proceedings of the 25th Annual IEEE Symposium on Logic in Computer Science (LICS 2010)*, IEEE Computer Society, 2010, pp. 160–169, doi:[10.1109/LICS.2010.10](https://doi.org/10.1109/LICS.2010.10); read as arXiv:1001.2086v1, whose numbering is used here: Section 2 (convolution, FA recognizable relations, automatic structures and presentations) and Theorem 1.
