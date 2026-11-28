# Church games with register-automaton specifications over the naturals are undecidable

When both players of a Church synthesis game pick natural numbers and the specification is a deterministic register automaton that compares data with the order of $\mathbb N$, no algorithm decides whether the system player wins.

**Theorem (Exibard, Filiot and Khalimov).** A *test* over a finite set $R$ of registers is a maximal consistent conjunction of atoms $\ast \bowtie r$ with $r \in R$ and $\bowtie \in \{=, <, >\}$, where $\ast$ stands for the incoming datum. A *deterministic register automaton* over $(\mathbb N, \le)$ is a tuple $S = (Q, q_\iota, R, \delta, \alpha)$ where $Q = Q_A \uplus Q_E$ is a finite set of states split into Adam and Eve states, $q_\iota \in Q_A$ is initial, $\delta$ is a total deterministic transition function mapping a state of $Q_A$ (of $Q_E$) and a test to a set of registers to overwrite and a state of $Q_E$ (of $Q_A$), and $\alpha : Q \to \{1, \dots, c\}$ is a priority function. On an infinite sequence $d_0 d_1 \cdots$ of natural numbers it runs from the state $q_\iota$ with all registers $0$: at each step it takes the unique test satisfied by the current datum and register contents, stores the datum in the registers named by $\delta$ and moves to the next state; the sequence is accepted if the largest priority visited infinitely often is even. In the *Church synthesis game* with specification $S$, Adam and Eve alternately choose natural numbers $i_0, o_0, i_1, o_1, \ldots$, Adam first, each seeing all previous choices; Eve wins the play if $i_0 o_0 i_1 o_1 \cdots$ is accepted by $S$. There is no algorithm that decides, given $S$, whether Eve has a winning strategy (Theorem 1 of the source).

The games become decidable, over $(\mathbb Q, \le)$ and over $(\mathbb N, \le)$, for *one-sided* specifications, in which Eve plays letters from a finite alphabet instead of data, so that only Adam's data are compared with registers (Definition 1, Theorem 2, and Theorems 9 for $(\mathbb Q, \le)$ and 18 for $(\mathbb N, \le)$ of the source).

## Depends on

- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Even max-parity condition](../parity-condition-on-infinite-sequences/parity-even.md)

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem of two-counter machines, using a specification with four registers $r_1, r_2, z, t$: $r_1$ and $r_2$ hold the counter values, $z$ holds $0$ for zero tests, and $t$ serves as a temporary register. Eve plays the successive counter values of the machine's run. An increment of the first counter is checked using that $c' = c + 1$ holds exactly when no datum lies strictly between $c$ and $c'$: Eve proposes a value $d > r_1$, stored in $t$, and Eve has cheated iff Adam can answer with a datum $d'$ such that $r_1 < d' < d$; otherwise $d$ is stored in $r_1$. Decrements and the second counter are handled similarly, and the winning condition asks that a halting instruction is eventually reached. If the machine halts, its counters stay bounded and Eve wins by playing the faithful run; if it does not halt, no halting instruction is reachable by a faithful simulation, and Adam catches every cheat.

## Sources

- L. Exibard, E. Filiot and A. Khalimov, "Church synthesis on register automata over linearly ordered data domains", *Formal Methods in System Design* 61(2–3):290–337, 2022, doi:[10.1007/s10703-023-00435-w](https://doi.org/10.1007/s10703-023-00435-w); read as arXiv:2004.12141v7, whose numbering is used here: Section 2 (tests and deterministic register automata), Section 3 (Church synthesis games), Theorem 1 with its proof idea and proof, Definition 1, and Theorems 2, 9 and 18. A conference version appeared in *38th International Symposium on Theoretical Aspects of Computer Science (STACS 2021)*, Leibniz International Proceedings in Informatics 187.
