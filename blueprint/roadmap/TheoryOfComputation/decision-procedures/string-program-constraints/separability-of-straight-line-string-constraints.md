# Separability of straight-line string constraints

Whether the solution sets of two straight-line string constraints can be separated by a regular relation is undecidable, but separation by piecewise testable relations, which only look at scattered subwords, is decidable; separators act as interpolants for string constraints.

Let $\Sigma$ be a finite alphabet and $x_1, \dots, x_n$ string variables. An atomic constraint is a membership $x \in L(A)$, with $A$ a finite automaton, or a relational constraint $(x, t) \in R(T)$, with $t$ a concatenation of variables and $T$ a transducer (a 2-tape automaton), also written $x = T(t)$: the value of $x$ is an output of $T$ on the value of $t$. A conjunction $\Psi$ of atomic constraints is a *straight-line (SL) formula* if it can be written as $\Psi_0 \wedge \bigwedge_{i=1}^k \varphi_i$, where $\Psi_0$ is a conjunction of memberships and, for distinct variables $x_1, \dots, x_n$ with $n \ge k$, each $\varphi_i$ is $(x_i, t_i) \in R(T_i)$ and every variable $x_j$ occurring in $t_i$ has $j > i$. Its *language* $L(\Psi) \subseteq (\Sigma^*)^n$ is the set of tuples of values of $x_1, \dots, x_n$ over all solutions.

For classes of relations $\mathcal{C}$ and $\mathcal{S}$, two relations $I, E \in \mathcal{C}$ over the same tuple of variables are *$\mathcal{S}$-separable* if some $S \in \mathcal{S}$ has $I \subseteq S$ and $S \cap E = \emptyset$.

- An $n$-ary relation is *regular* (REG) here if it is a finite union of products $L_1 \times \dots \times L_n$ of regular languages.
- An $n$-ary relation is *$n$-PTL* if it is a finite Boolean combination of sets $(\Sigma^*)^n v_1 (\Sigma^*)^n \cdots v_k (\Sigma^*)^n$ with $v_1, \dots, v_k \in (\Sigma \cup \{\varepsilon\})^n$ and componentwise concatenation; each such set is the product, over the coordinates, of the piece languages of the component words of $v_1 \cdots v_k$, so for $n = 1$ these are the [piecewise testable languages](../../regular-languages/syntactic-monoids/varieties-and-algebraic-characterizations/piecewise-testable-languages.md).

Then:

1. REG-separability of two SL formulas over the same variables is undecidable (with the alphabet part of the input).
2. $n$-PTL-separability of two SL formulas over the variables $x_1, \dots, x_n$ is decidable.

If $L(\Psi) \subseteq S$ and $S \cap L(\Psi') = \emptyset$, then $\Psi \wedge \Psi'$ is unsatisfiable, so a separator certifies unsatisfiability; every string constraint is equisatisfiable with a conjunction of two SL formulas.

## Depends on

- [Rational relations and transducers](../../regular-languages/automata-and-expressions/rational-relations-and-transductions/rational-relations-and-transducers.md)
- [Piecewise testable languages](../../regular-languages/syntactic-monoids/varieties-and-algebraic-characterizations/piecewise-testable-languages.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

This node still needs its proof broken down. Part 1 is the source's Theorem 2, proved in Appendix B of the full version by reduction from the halting problem of deterministic Turing machines. For a machine $M$ with initial configuration $w_1$, configurations are encoded as words, and letters $a, \#, \diamond$ outside the tape alphabet are added ($\diamond$ is written as a dollar sign in the source). One builds transducers $T_1, T_2$ such that the SL formulas $\Psi_1 = (x, y \diamond y) \in R(T_1)$ and $\Psi_2 = (x, y \diamond y) \in R(T_2)$ (the source writes $\Psi_1$ for both, a typo) have the languages

$$
L(\Psi_1) = \{(w_1 \# w_3 \# \cdots \# w_{2k-1} \diamond a^k,\ w_2 \# w_4 \# \cdots \# w_{2k} \#) : k \ge 1,\ w_{2i-1} \to_M w_{2i} \text{ for } i \le k\}
$$

and $L(\Psi_2)$, the same with $a^{2k}$ in place of $a^k$ and the condition $w_{2i-2} = w_{2i-1}$ for $2 \le i \le k$ in place of the transition steps; here each $w_i$ is a configuration and $w \to_M w'$ is one step of $M$. If $M$ does not halt, let $u_1 = w_1 \to_M u_2 \to_M u_3 \to_M \cdots$ be its run, suppose a finite union of products $L_i \times L'_i$ of regular languages separates the two languages, let $n - 1$ be the total number of states of deterministic automata for the $L_i$, and put $k = n!$. Taking $w_{2i-1} = u_i$ and $w_{2i} = u_{i+1}$ for $i \le k$, so that the first track is $u_1 \# \cdots \# u_k$ and the second $u_2 \# \cdots \# u_{k+1} \#$, gives a word pair in $L(\Psi_1)$ with suffix $a^k$ (each $w_{2i-1} \to_M w_{2i}$ is a step of the run) and in $L(\Psi_2)$ with suffix $a^{2k}$ (each $w_{2i-2} = u_i = w_{2i-1}$); these are the source's witnesses, built from $n!$ steps of the run. The first pair lies in some $L_i \times L'_i$; reading $a^k$ the automaton for $L_i$ repeats a state with a loop of length at most $n$, which divides $k$, so it also accepts the first component with its suffix $a^k$ replaced by $a^{2k}$, and the second pair lies in the separator too, a contradiction. If $M$ halts, with run $u_1 \to_M \cdots \to_M u_n$ of $n$ configurations ($n - 1$ steps) ending in a configuration with no successor, the separator is the union of two families of products. For $i \le n$, the products whose first component has $i$ configurations and $i$ letters $a$ and whose second has $i$ configurations: they cover the pairs of $L(\Psi_1)$ with at most $n$ configurations per track and miss $L(\Psi_2)$, whose pairs with $i$ configurations have $2i$ letters $a$. For $j \le n$, the products whose first track starts with $u_1, \dots, u_{j-1}$ followed by one configuration different from the fixed word $u_j$, and whose second track starts with $u_2, \dots, u_j$, both followed by arbitrary configurations: these detect a first failure of the copy condition at position $j$, against a fixed configuration, so they miss $L(\Psi_2)$; and every pair of $L(\Psi_1)$ with more than $n$ configurations has such a first failure at some $j \le n$, since otherwise its tracks would follow the run beyond $u_n$, which has no successor. The terms of this page contain only variables, so the letter $\diamond$ in $y \diamond y$ is written as a fresh variable $z$ with the membership $z \in \{\diamond\}$; the formulas $(x, y z y) \in R(T_i) \wedge z \in \{\diamond\}$ are SL formulas over $x, y, z$, and since $z$ is fixed to $\diamond$, they are REG-separable iff the source's formulas are. Part 2 (Theorem 11): solutions of an SL formula are encoded, as words $u_1 \# \cdots \# u_n$, by an ordered multi-pushdown automaton that guesses the source variables in its stacks and simulates the transducers from the last constraint to the first (Lemmas 8–9); $n$-PTL-separability of two SL formulas is equivalent to PTL-separability of the two encodings (Lemma 10). Ordered multi-pushdown languages form a full trio (Lemma 3) with effectively semilinear Parikh images (Lemma 5); for such classes PTL-separability is equivalent to the diagonal problem (Lemma 4), which is decidable (Theorem 6). The source leaves the complexity of part 2 open.

## Sources

- P. A. Abdulla, M. F. Atig, V. Dave and S. N. Krishna, "On the separability problem of string constraints", 31st International Conference on Concurrency Theory (CONCUR 2020), LIPIcs 171, Article 16, 2020, doi:[10.4230/LIPIcs.CONCUR.2020.16](https://doi.org/10.4230/LIPIcs.CONCUR.2020.16); full version arXiv:2005.09489v2, <https://arxiv.org/abs/2005.09489v2>: numbering of the published version, Section 2 (string constraints, SL formulas, Lemma 1, the separability problem), Section 3 (REG and Theorem 2), and Section 4 (piece languages and $n$-PTL, Lemmas 3–5 and 8–10, Theorems 6 and 11); full version Appendix B (proof of Theorem 2).
