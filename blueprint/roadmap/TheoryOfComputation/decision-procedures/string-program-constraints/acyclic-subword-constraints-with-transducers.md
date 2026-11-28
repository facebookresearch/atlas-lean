# Acyclic subword constraints with transducers

String constraints in which each variable must be a scattered subword of a shuffle of transductions of other variables, with pushdown or finite-automaton memberships, are decidable when the subword constraints are acyclic: 2NEXPTIME-complete in general and NEXPTIME-complete when all memberships are regular.

Let $\Sigma$ be a finite alphabet. Write $u \preceq w$ when $u$ is a scattered subword of $w$, and for a finite multiset $\{\{u_1, \dots, u_n\}\}$ of words let $\mathrm{Shuffle}(\{\{u_1, \dots, u_n\}\})$ be the set of words whose positions split into $n$ disjoint sets spelling $u_1, \dots, u_n$ (for two words this is the [shuffle of two words](../../regular-languages/automata-and-expressions/closure-properties-of-regular-languages/is-shuffle.md)). A *transducer* here is a nondeterministic finite automaton whose transitions read a letter or $\varepsilon$ and emit a word; it relates the input read to the output emitted along an accepting run.

A *string constraint* $C = (\Sigma, V, \mathrm{Mem}, \mathrm{Rel})$ consists of a finite set $V$ of variables; a map $\mathrm{Mem}$ assigning to each variable a pushdown automaton or a nondeterministic finite automaton; and a finite set $\mathrm{Rel}$ of *subword-order constraints* $(x, Y)$, where $x \in V$ and $Y$ is a finite multiset of pairs $(y, T)$ with $y \in V$ and $T$ a transducer, written $x \preceq \mathrm{Shuffle}(Y)$. An assignment $\sigma : V \to \Sigma^*$ satisfies $C$ if $\sigma(v) \in L(\mathrm{Mem}(v))$ for every $v$, and for every $(x, \{\{(y_1, T_1), \dots, (y_n, T_n)\}\}) \in \mathrm{Rel}$ there are words $u_1, \dots, u_n$, one for each occurrence in the multiset, with $(\sigma(y_i), u_i) \in R(T_i)$, and a word $w \in \mathrm{Shuffle}(\{\{u_1, \dots, u_n\}\})$ with $\sigma(x) \preceq w$. $C$ is *regular* if every $\mathrm{Mem}(v)$ is a finite automaton. Writing $x < y$ when some $(x, Y) \in \mathrm{Rel}$ has a pair $(y, T)$ in $Y$, $C$ is *acyclic* if the directed graph of $<$ has no cycle. The input lists the automata, transducers and every multiset occurrence explicitly. Let 2NEXPTIME be the class of problems decided by nondeterministic Turing machines in time $2^{2^{p(n)}}$ for a polynomial $p$.

1. Satisfiability of acyclic string constraints (memberships by pushdown or finite automata) is 2NEXPTIME-complete.
2. Satisfiability of acyclic regular string constraints is [NEXPTIME](../../complexity-classes/time-and-space-complexity-classes/nexp.md)-complete.

The upper bounds also hold with concatenation in place of shuffle, which shuffle simulates by a polynomial translation preserving acyclicity, and both lower bounds already hold without shuffle. Without acyclicity, satisfiability with shuffle is undecidable already for regular constraints with identity transducers only (an earlier result of the same authors).

## Depends on

- [Rational relations and transducers](../../regular-languages/automata-and-expressions/rational-relations-and-transductions/rational-relations-and-transducers.md)
- [Language accepted by a pushdown automaton](../../context-free-languages/grammars-and-pushdown-automata/pushdown-automata/accepts.md)
- [The complexity class NEXP](../../complexity-classes/time-and-space-complexity-classes/nexp.md)

## Proof depends on

None.

## Expansion

This node still needs its proof broken down; the source proofs have these parts.

Upper bound of part 1 (Section 5). Small model property (Theorem 17): a satisfiable acyclic constraint has a solution in which every value has length at most

$$
B = 2^{2^{O(m \log t + \log p + \log k)}},
$$

with $m$ the largest number of right-hand occurrences of a variable, $t$ the largest number of states of a transducer, $p$ the largest number of states plus stack symbols of a pushdown automaton (states of a finite automaton), and $k$ the number of variables; when a set over which a maximum is taken is empty, we take the maximum to be $1$ (our convention). Lemma 18 extends this to the transducer outputs witnessing each occurrence, bounded by $2 c t B$ with $c$ the longest word emitted by a transition; its proof processes the variables along the acyclic order, pruning and pumping runs. A procedure guesses such an extended assignment and checks memberships, transductions, and the subword-of-shuffle conditions, the latter in NP in the length of the words. Part 2's upper bound is proved in the full version (its Lemma 27 for the regular case).

Lower bound of part 1 (Section 4): reduce the bounded Post correspondence problem: given disjoint finite alphabets $\Sigma_1, \Sigma_2$, homomorphisms $f, g : \Sigma_1^* \to \Sigma_2^*$ and $\ell$ in unary, is there $w \in \Sigma_1^+$ with $f(w) = g(w)$ and $|f(w)| = 2^{2^\ell}$? It is 2NEXPTIME-complete (Theorem 11, proved in the full version). Pushdown memberships give $x_f \in \{w \#^* f(w^r)\}$ and $x_g \in \{w \#^* g(w^r)\}$, and the chain $x_1 \preceq x_f \preceq x_g \preceq x_2$ with length-fixing languages for $x_1, x_2$ forces $f(w) = g(w)$; the doubly exponential length is enforced by one pushdown automaton together with $\ell$ finite automata of size $O(\ell)$ applied through transducers (Claims 12–15), and Claim 16 proves the reduction correct. Part 2's lower bound uses the NEXPTIME-hardness of the acyclic fragment without transducers, from an earlier paper of the same authors.

## Sources

- C. Aiswarya, S. Mal and P. Saivasan, "Satisfiability of context-free string constraints with subword-ordering and transducers", 41st International Symposium on Theoretical Aspects of Computer Science (STACS 2024), LIPIcs 289, Article 5, 2024, doi:[10.4230/LIPIcs.STACS.2024.5](https://doi.org/10.4230/LIPIcs.STACS.2024.5): Section 2 (subwords, shuffle, transducers, pushdown automata), Section 3 (Definitions 1, 2 and 4, acyclicity), Theorems 5 and 6, Remarks 7–9 (Remark 9: a linear simulation of concatenation by shuffle), Section 4 (Definition 10, Theorem 11, Claims 12–16), and Section 5 (Theorem 17, Lemma 18); full version arXiv:2401.07996v1, <https://arxiv.org/abs/2401.07996v1>: proofs of Theorems 6 and 11, Lemma 27, and Section 7.2 (polynomial simulation of concatenation).
- C. Aiswarya, S. Mal and P. Saivasan, "On the satisfiability of context-free string constraints with subword-ordering", 37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022), doi:[10.1145/3531130.3533329](https://doi.org/10.1145/3531130.3533329): undecidability without acyclicity (with shuffle and identity transducers) and NEXPTIME-completeness of the acyclic fragment without transducers, as cited in Section 3 of the STACS 2024 paper.
