# Diagonal transducer constraints are undecidable

It is undecidable whether a transducer relates some word to itself. Hence satisfiability of string constraints with concatenation and transducers is undecidable, already for a single atom $R(x, x)$ or for $x = y \wedge R(x, y)$.

Use the string constraints of [string constraints with concatenation and transducers](string-constraints-with-concatenation-and-transducers.md). There is a finite alphabet $\Sigma$ for which no algorithm decides, given a transducer realizing a [rational relation](../../regular-languages/automata-and-expressions/rational-relations-and-transductions/rational-relations-and-transducers.md) $R \subseteq \Sigma^* \times \Sigma^*$, whether $(w, w) \in R$ for some word $w$, that is, whether the constraint $R(x, x)$ is satisfiable. Since $x = y \wedge R(x, y)$ is satisfiable exactly when $R(x, x)$ is, satisfiability of string constraints of that form, and of string constraints in general, is undecidable.

## Depends on

- [String constraints with concatenation and transducers](string-constraints-with-concatenation-and-transducers.md)
- [Rational relations and transducers](../../regular-languages/automata-and-expressions/rational-relations-and-transductions/rational-relations-and-transducers.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Given dominoes $(a_1, b_1), \dots, (a_n, b_n)$ over $\Sigma$, let $D = \{(a_1, b_1), \dots, (a_n, b_n)\}$, a finite and hence rational relation, and $R = D \cdot D^*$, where the product of pairs is componentwise concatenation; $R$ is rational because rational relations are closed under product and star, and a transducer for it is built from $n$ branches spelling $(a_i, b_i)$ that may be repeated, with acceptance only after at least one branch has been taken. Its pairs are exactly $(a_{i_1} \cdots a_{i_k}, b_{i_1} \cdots b_{i_k})$ with $k \ge 1$, so $(w, w) \in R$ for some $w$ exactly when the instance has a solution, a nonempty index sequence whose tops and bottoms concatenate to the same word (possibly empty, if the dominoes allow it). The construction is computable, so a decider for diagonal nonemptiness would decide the Post correspondence problem over $\Sigma$.

## Sources

- A. W. Lin and P. Barceló, "String solving with word equations and transducers: towards a logic for analysing mutation XSS", POPL 2016, pp. 123–136, doi:[10.1145/2837614.2837641](https://doi.org/10.1145/2837614.2837641); full version arXiv:1511.01633v1, <https://arxiv.org/abs/1511.01633v1>: Section 3.2, Proposition 1 and the paragraph after it (the form $R(x, x)$, by reduction from the Post correspondence problem), and the paragraph after Proposition 2 (the form $x = y \wedge R(x, y)$).
- L. Holík, P. Janků, A. W. Lin, P. Rümmer and T. Vojnar, "String constraints with concatenation and transducers solved efficiently", Proceedings of the ACM on Programming Languages 2 (POPL), Article 4, 2018, doi:[10.1145/3158092](https://doi.org/10.1145/3158092); technical report arXiv:2010.15975v1, <https://arxiv.org/abs/2010.15975v1>: Section 3.1 (the encoding of the Post correspondence problem as $R(x, x)$).
