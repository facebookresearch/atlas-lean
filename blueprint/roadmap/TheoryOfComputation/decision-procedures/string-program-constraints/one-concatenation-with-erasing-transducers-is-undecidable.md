# One concatenation with erasing transducers is undecidable

Adding a single concatenation to an acyclic conjunction of regular constraints and letter-erasing transducers makes satisfiability undecidable, so acyclicity of the transducer atoms alone does not survive word equations.

Use the string constraints of [string constraints with concatenation and transducers](string-constraints-with-concatenation-and-transducers.md). For a finite alphabet $\Gamma$ and $A \subseteq \Gamma$, the *erasing transduction* $\mathrm{erase}_A$ maps a word to the word obtained by deleting every occurrence of a letter of $A$; it is realized by a one-state transducer with transitions labelled $(a, \varepsilon)$ for $a \in A$ and $(b, b)$ for $b \in \Gamma \setminus A$. Call a conjunction of atoms $P(x)$ and $R(x, y)$ *acyclic* if $x \neq y$ in every atom $R(x, y)$ and the undirected multigraph on the variables with one edge $\{x, y\}$ for each atom $R(x, y)$ has no cycle.

There is no algorithm that decides, given a finite alphabet $\Gamma$ and a constraint $x = y z \wedge \varphi$ over $\Gamma$, where $\varphi$ is an acyclic conjunction of regular atoms and atoms $v = \mathrm{erase}_A(u)$ with $A \subseteq \Gamma$, whether it is satisfiable. The alphabet $\Gamma$ is part of the input: the reduction adds one fresh letter per domino.

## Depends on

- [String constraints with concatenation and transducers](string-constraints-with-concatenation-and-transducers.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Let $(a_1, b_1), \dots, (a_n, b_n)$ be dominoes over $\Sigma$. If some domino has $a_i = b_i = \varepsilon$, the instance has the solution $i$; output a fixed satisfiable constraint. Otherwise every solution $i_1, \dots, i_k$ has a nonempty common word $a_{i_1} \cdots a_{i_k} = b_{i_1} \cdots b_{i_k}$, since an empty one would force every chosen domino to be empty on both sides. (This preliminary case split repairs a corner case of the source's reduction: its dominoes are arbitrary words over $\Sigma$, but its constraint requires $x_2 \in \Gamma^+$, which a solution with empty common word would violate.)

Take fresh letters $1, \dots, n$, put $\Gamma = \Sigma \cup \{1, \dots, n\}$, $A = \{1, \dots, n\}$, $B = \Sigma$, and the constraint

$$
x_2 = \mathrm{erase}_A(x_1) \wedge x_3 = \mathrm{erase}_B(x_1) \wedge x_2 = \mathrm{erase}_A(x_4) \wedge x_3 = \mathrm{erase}_B(x_5) \wedge x_4 = x_6 x_5
$$

with $x_1 \in (\bigcup_i a_i i)^+$, $x_4 \in (\bigcup_j b_j j)^+$, $x_6 \in \{\varepsilon\}$ and $x_2, x_3, x_5 \in \Gamma^+$. The transducer edges $x_4 x_2$, $x_2 x_1$, $x_1 x_3$, $x_3 x_5$ form a path, so $\varphi$ is acyclic. If an assignment satisfies it, $x_6 = \varepsilon$ gives $x_4 = x_5$; writing $x_1 = a_{i_1} i_1 \cdots a_{i_k} i_k$ and $x_4 = b_{j_1} j_1 \cdots b_{j_p} j_p$, erasing indices gives $a_{i_1} \cdots a_{i_k} = b_{j_1} \cdots b_{j_p}$ and erasing letters of $\Sigma$ gives $i_1 \cdots i_k = j_1 \cdots j_p$, a solution. Conversely a solution $i_1, \dots, i_k$ gives the assignment $x_1 = a_{i_1} i_1 \cdots a_{i_k} i_k$, $x_2 = a_{i_1} \cdots a_{i_k}$ (nonempty by the case split), $x_3 = i_1 \cdots i_k$, $x_4 = x_5 = b_{i_1} i_1 \cdots b_{i_k} i_k$ and $x_6 = \varepsilon$.

## Sources

- A. W. Lin and P. Barceló, "String solving with word equations and transducers: towards a logic for analysing mutation XSS", POPL 2016, pp. 123–136, doi:[10.1145/2837614.2837641](https://doi.org/10.1145/2837614.2837641); full version arXiv:1511.01633v1, <https://arxiv.org/abs/1511.01633v1>: Example 2 (the erasing transducer), Section 3.2, Proposition 3, and the appendix proof of Proposition 3 (constraint (2) and the languages $L_1, \dots, L_6$).
