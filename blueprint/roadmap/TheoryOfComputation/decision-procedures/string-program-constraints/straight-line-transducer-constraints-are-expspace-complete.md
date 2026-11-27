# Straight-line transducer constraints are EXPSPACE-complete

Satisfiability of straight-line string constraints with concatenation, transducers and Boolean regular constraints is EXPSPACE-complete, and every satisfiable such constraint has a solution whose words have at most doubly exponential length.

Let $\mathrm{SL}$ be the class of [straight-line string constraints](straight-line-string-constraints.md) over a finite alphabet $\Sigma$: a straight-line conjunction of assignments $x_i = y_1 \cdots y_n$ ($n \ge 1$) and $x_i = R(y)$, with $R$ given by a transducer, together with a Boolean combination of atoms $P(x)$ with $P$ given by a nondeterministic finite automaton; sizes are those of the explicitly written constraint.

1. The satisfiability problem for $\mathrm{SL}$ is [EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md)-complete.
2. There is a polynomial $p$ such that every satisfiable $\varphi \in \mathrm{SL}$ has a solution in which every word has length at most $2^{2^{p(|\varphi|)}}$.

The lower bound already holds with functional transducers.

## Depends on

- [Straight-line string constraints](straight-line-string-constraints.md)
- [The class EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md)

## Proof depends on

- [Acyclic transducer constraints are PSPACE-complete](acyclic-transducer-constraints-are-pspace-complete.md)
- [Savitch's theorem](../../complexity-classes/savitch.md)

## Expansion

This node still needs its proof broken down; the source proof has these parts.

Step 1 (normalization of the regular constraint). Enumerate, in polynomial space, the satisfying assignments of the regular constraint viewed as a propositional formula, and guess one; complement the automata of negative literals and intersect the automata on a common variable by products, so that every variable carries one automaton. This step is exponential in time and in the size of the automata, independently of the rest.

Step 2 (removing concatenation; Lemmas 7–8). Process the variables in a topological order of the dependency graph, with source variables first, and give each variable $y$ fresh copies $y(1), \dots, y(\max_y)$, meant to spell $y$ as $y(1) \cdots y(\max_y)$: a source variable gets $\max_y = 1$; for $y = y_1 \cdots y_n$ the copies of $y$ are those of $y_1, \dots, y_n$ in order, each linked by the identity transducer, so $\max_y = \sum_j \max_{y_j}$, counting repeated occurrences; for $y = R(x)$, $\max_y = \max_x$ and the atom becomes the disjunction, over sequences $p_0, \dots, p_{\max_y}$ of states of the transducer with $p_0$ initial, $p_{\max_y}$ final and each $p_i$ reachable from $p_{i-1}$, of the conjunctions of $y(i) = R_{[p_{i-1}, p_i]}(x(i))$, where $R_{[p, q]}$ is $R$ started in $p$ and accepting only in $q$. The automaton $P$ on $y$ is split in the same way along state sequences from an initial to a final state. Lemma 8 shows, by induction along the order, that an assignment satisfies the part of $\varphi$ up to $y$ iff some assignment of the copies satisfies the transformed part and spells each variable as the concatenation of its copies; so solutions translate in both directions.

Step 3 (Lemma 9 and the bound). Guess one disjunct of each split. Each copy $y(k)$ is then the output of at most one transducer atom, whose input is a copy of an earlier variable; directed edges go from earlier to later copies and every copy has in-degree at most one, so the undirected graph of transducer atoms is a forest and the result is an acyclic conjunction. Its size is $O(\mathrm{Dim}(\varphi) \cdot |\varphi|)$ in the normalized automata, where the dimension $\mathrm{Dim}(\varphi)$, the largest $\max_y$, can be exponential in $|\varphi|$ (for example $x_{i+1} = x_i x_i$). Deciding it in space polynomial in its own size, with the guesses removed by Savitch's theorem, takes space exponential in $|\varphi|$; the exponential solution bound for acyclic conjunctions, applied to this exponential formula, and reassembly of copies give part 2.

Lower bound. A deterministic Turing machine working in space $2^{cn}$ is encoded: a regular constraint on $x$ says that $x$ spells a sequence of configurations from the initial to an accepting one, equations $y = x x$ iterated make exponentially many copies of $x$, and transducers delete chosen parts so that regular constraints compare each configuration with the next. The full reduction is in the source's appendix; its transducers are functional.

## Sources

- A. W. Lin and P. Barceló, "String solving with word equations and transducers: towards a logic for analysing mutation XSS", POPL 2016, pp. 123–136, doi:[10.1145/2837614.2837641](https://doi.org/10.1145/2837614.2837641); full version arXiv:1511.01633v1, <https://arxiv.org/abs/1511.01633v1>: Theorem 5 and Theorem 6, Section 4.2.1 (Steps 1–3, Lemmas 7–9), Section 4.2.2 (proof of Theorem 6, the dimension), Section 4.2.3 (lower-bound sketch) and the appendix (full lower-bound reduction).
- T. Chen, M. Hague, A. W. Lin, P. Rümmer and Z. Wu, "Decision procedures for path feasibility of string-manipulating programs with complex operations", Proceedings of the ACM on Programming Languages 3 (POPL), Article 49, 2019, doi:[10.1145/3290362](https://doi.org/10.1145/3290362); arXiv:1811.03167v1, <https://arxiv.org/abs/1811.03167v1>: Section 5.1, the sentence after Proposition 5.4 (the EXPSPACE-hardness reduction of Lin and Barceló uses only functional transducers).
