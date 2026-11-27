# Higher-dimensional timed automata and their languages

A higher-dimensional timed automaton is a higher-dimensional automaton, whose cells stand for sets of concurrently running
events, equipped with a clock invariant and a set of clocks to reset on exit for each cell; time may pass in any cell, so actions
take time, and its language is a set of timed interval pomsets.

**Higher-dimensional automata.** A *conclist* over a finite alphabet $\Sigma$ is a finite set $U$ of events with a strict total order
and a labeling $U \to \Sigma$. A *precubical set* $X$ on $\Sigma$ is a set of cells with a map $\mathrm{ev}$ assigning a conclist to each cell
and, for every conclist $U$ and $A \subseteq U$, *lower* and *upper face maps* $\delta^0_A, \delta^1_A$ from the cells with events $U$ to the
cells with events $U \setminus A$, satisfying $\delta^\nu_A \delta^\mu_B = \delta^\mu_B \delta^\nu_A$ for disjoint $A, B$; the lower face $\delta^0_A(x)$ is
the cell before the events of $A$ start and the upper face $\delta^1_A(x)$ the cell after they terminate. A *higher-dimensional automaton*
(HDA) $(\Sigma, X, \bot, \top)$ is a finite precubical set with sets $\bot, \top$ of initial and accepting cells. A finite automaton is a
one-dimensional HDA whose initial and accepting cells have no events.

**HDTAs.** A *higher-dimensional timed automaton* (HDTA) $(\Sigma, C, Q, \bot, \top, \mathrm{inv}, \mathrm{exit})$ is a finite HDA
$(\Sigma, Q, \bot, \top)$ with a finite set $C$ of clocks, an *invariant* $\mathrm{inv}(q)$, a clock constraint, and an *exit set*
$\mathrm{exit}(q) \subseteq C$ for each cell $q$. Its operational semantics has configurations $(q, v)$ with $v \in \mathbb{R}_{\ge 0}^C$
satisfying $\mathrm{inv}(q)$, initial configurations $(q, 0)$ with $q \in \bot$ and accepting configurations with $q \in \top$, and three kinds of
moves: a *delay* by $d \ge 0$ inside a cell, allowed when the invariant stays satisfied throughout; *starting* the events $A \subseteq \mathrm{ev}(q)$ from
$(\delta^0_A(q), v)$ to $(q, v')$ with $v' = v[\mathrm{exit}(\delta^0_A(q)) \gets 0]$ satisfying $\mathrm{inv}(q)$; and *terminating* them from
$(q, v)$ to $(\delta^1_A(q), v')$ with $v' = v[\mathrm{exit}(q) \gets 0]$ satisfying $\mathrm{inv}(\delta^1_A(q))$.

**Languages.** An accepting path is a finite sequence of consecutive moves from an initial to an accepting configuration. Its
*observable content* is the timed interval pomset (tipomset) obtained by gluing the contributions of its moves: a delay by $d$ in a cell
contributes the identity on the events of that cell, each running for time $d$, and a start or a termination contributes the
corresponding starter or terminator with duration $0$. The *language* $\mathcal{L}(A)$ of an HDTA $A$ is the set of observable contents of
its accepting paths; equivalently, it can be presented by interval delay words.

**Timed automata as HDTAs.** For a timed automaton $A$ over finite timed words (in the source, with location invariants and accepting locations), the HDTA $H(A)$ has one cell for each location and one
for each transition, uses an extra clock forcing transitions to take zero time, and satisfies $\mathcal{L}(H(A)) = \{i_1(w) : w \in \mathcal{L}(A)\}$,
where $i_1$ maps a delay word to the interval delay word it induces.

## Depends on

- [Timed automata over finite timed words](../decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md)

## Proof depends on

None.

## Sources

- A. Amrane, H. Bazille, E. Clement, U. Fahrenberg and P. Schlehuber-Caissier, "Higher-dimensional timed automata for real-time concurrency", in *Design and Verification of Cyber-Physical Systems: From Theory to Applications*, Lecture Notes in Computer Science 16060, pp. 66–100, Springer, 2026, doi:10.1007/978-3-032-16855-9_4; read in arXiv:2401.17444v4: Section 3 (conclists, precubical sets, HDAs), Section 4 (the definition of HDTAs and their operational semantics), Section 7 (paths, observable content and languages) and Section 8 (the translation $H$ and its language theorem).
