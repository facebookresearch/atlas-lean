# String constraints with concatenation and transducers

A string constraint with concatenation and transducers is a conjunction of relational atoms (a variable equals a concatenation of variables or a constant word, or two variables are related by a rational relation given by a transducer) with a Boolean combination of regular-membership atoms; it is satisfiable when some assignment of words makes it true.

Fix a finite alphabet $\Sigma$ and countably many string variables $x, y, z, \dots$ ranging over $\Sigma^*$.

- An *atomic relational constraint* is $y = x_1 \cdots x_n$ (with $n \in \mathbb{N}$ and $y, x_1, \dots, x_n$ variables, not necessarily distinct), $y = w$ with $w \in \Sigma^*$ a constant word, or $R(x, y)$, where $R \subseteq \Sigma^* \times \Sigma^*$ is a [rational relation](../../regular-languages/automata-and-expressions/rational-relations-and-transductions/rational-relations-and-transducers.md) given by a transducer. A *relational constraint* is a finite conjunction of atomic relational constraints.
- An *atomic regular constraint* is $P(x)$, where $P \subseteq \Sigma^*$ is the language of a given nondeterministic finite automaton (finitely many states, initial and final states, and letter-labelled transitions; $P$ is the set of words labelling a path from an initial to a final state). A *regular constraint* is a Boolean combination (with $\wedge$, $\vee$, $\neg$) of atomic regular constraints.
- A *string constraint* is the conjunction of a relational constraint and a regular constraint.

An *assignment* $\iota$ maps the variables of a constraint $\varphi$ to words of $\Sigma^*$. It satisfies $y = x_1 \cdots x_n$ when $\iota(y) = \iota(x_1) \cdots \iota(x_n)$ (for $n = 0$ the right side is the empty word), $y = w$ when $\iota(y) = w$, $R(x, y)$ when $(\iota(x), \iota(y)) \in R$, and $P(x)$ when $\iota(x) \in P$; Boolean connectives have their usual meaning. A satisfying assignment is a *solution*, and *satisfiability* is the problem: given a string constraint $\varphi$, does it have a solution? The input is written explicitly: words letter by letter, and each automaton and transducer by its states and its list of transitions with their labels.

General word equations $x_1 \cdots x_n = y_1 \cdots y_m$ are expressed by two equations $z = x_1 \cdots x_n \wedge z = y_1 \cdots y_m$ with a fresh variable $z$. A transducer atom $R(x, y)$ is often written $y = R(x)$, though $R$ is a relation and need not be a function.

## Depends on

- [Rational relations and transducers](../../regular-languages/automata-and-expressions/rational-relations-and-transductions/rational-relations-and-transducers.md)

## Proof depends on

None.

## Expansion

This is a definition, following the source's core constraint language. Concatenation and transducers are genuinely different primitives: an equation $y = x_1 x_2$ with distinct variables relates three words and is not in general expressible by a binary atom on its variables, while a transducer atom is binary. (With repeated variables, such as $y = x x$, the equation is a binary relation, rational over a one-letter alphabet but not in general.) The source treats an equation $y = w$ as the regular constraint $y \in \{w\}$ when convenient.

## Sources

- A. W. Lin and P. Barceló, "String solving with word equations and transducers: towards a logic for analysing mutation XSS", Proceedings of the 43rd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2016), pp. 123–136, doi:[10.1145/2837614.2837641](https://doi.org/10.1145/2837614.2837641); full version arXiv:1511.01633v1, <https://arxiv.org/abs/1511.01633v1>: Section 3.1, Definitions 1–3 and the satisfaction clauses 1–4, and Section 3.2 (the problem SATISFIABILITY).
