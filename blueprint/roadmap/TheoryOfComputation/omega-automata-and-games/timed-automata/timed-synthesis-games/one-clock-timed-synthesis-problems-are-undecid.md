# One-clock timed synthesis problems are undecidable

In timed Büchi–Landweber games whose winning condition is given by a one-clock nondeterministic timed Büchi automaton, the existence of a winning strategy is undecidable for every choice of the player who owns the condition and the player who seeks to win, and so is the existence of a winning finite-memory controller in all cases but one. In that case, Timer owning the condition and Monitor seeking a controller, undecidability holds once both the winning condition and the controllers may use a slight extension, 1-resetting one-clock automata.

**Timed games.** A *timed word* over a finite alphabet $\Sigma$ is an infinite sequence $(a_1, t_1)(a_2, t_2) \cdots$ of letters with non-decreasing rational timestamps. A *timed game* $(\Sigma_T, \Sigma_M, \mathcal{A}, \mathrm{Owner}, \mathrm{Agent})$ has finite alphabets $\Sigma_T$ and $\Sigma_M$ of two players, Timer and Monitor, a nondeterministic timed automaton $\mathcal{A}$ with Büchi acceptance over $\Sigma_T \times \Sigma_M$, and $\mathrm{Owner}, \mathrm{Agent} \in \{\mathrm{Timer}, \mathrm{Monitor}\}$. In round $i$, Timer chooses $a_i \in \Sigma_T$ and a delay $\tau_i \in \mathbb{Q}_{\ge 0}$, then Monitor chooses $b_i \in \Sigma_M$; the play is the timed word $(a_1, b_1, t_1)(a_2, b_2, t_2) \cdots$ with $t_i = \tau_1 + \dots + \tau_i$. The Owner wins a play if it belongs to the language of $\mathcal{A}$, and its opponent wins otherwise. A *strategy* of Timer maps the sequence of Monitor's past letters to its next move; a strategy of Monitor maps the sequence of Timer's past moves to a letter. A *controller* is a finite-memory strategy: for Monitor, a deterministic timed automaton with outputs in $\Sigma_M$; for Timer, a deterministic finite automaton with outputs in $\Sigma_T \times \mathbb{Q}_{\ge 0}$ and an initial move. *Timed reactive synthesis* asks whether the Agent has a winning strategy, *timed Church synthesis* whether it has a winning controller. Let $\mathrm{NTA}_1$ denote nondeterministic timed automata with one clock.

**Theorem (Lasota, Lehaut, Parreaux and Piórkowski).** Let the winning condition be given by an automaton $\mathcal{A} \in \mathrm{NTA}_1$ and let Monitor be the Owner. Then timed reactive synthesis is undecidable for either Agent, and timed Church synthesis is undecidable when Monitor is the Agent (Theorem 13 of the source).

The source completes the picture in all other cases. With Monitor as the Owner, timed Church synthesis is also undecidable when Timer is the Agent (Theorem 15). With Timer as the Owner, timed reactive synthesis is undecidable for either Agent and timed Church synthesis is undecidable when Timer is the Agent (Theorem 16). With Timer as the Owner and Monitor as the Agent, timed Church synthesis is undecidable in the 1-resetting model of Section 6 (Theorem 23): the winning condition is given by a *1-resetting* one-clock reachability automaton, which extends a one-clock reachability timed automaton by $\varepsilon$-transitions that reset the clock whenever it reaches the value $1$, and Monitor's controllers are 1-resetting deterministic timed automata with outputs (the winning controller built in the proof of Theorem 27 is of this kind).

This last case is the one in which the source leaves the plain model, for both the winning condition and the controllers. The source states that analogous results hold for one-register automata over data words.

## Depends on

- [Timed Büchi automata and timed regular languages](../timed-buchi-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Four reductions cover the eight problems. When Monitor owns the condition, the problems reduce from universality and sampled universality of one-clock timed automata over infinite words, both undecidable. When Timer owns the condition, the reductions start from repeated reachability and from boundedness of lossy counter machines, both undecidable. A good expansion links pages for these four problems.

## Sources

- S. Lasota, M. Lehaut, J. Parreaux and R. Piórkowski, "One-Clock Synthesis Problems", in *43rd International Symposium on Theoretical Aspects of Computer Science (STACS 2026)*, Leibniz International Proceedings in Informatics (LIPIcs) 364, 2026, paper 64, doi:10.4230/LIPIcs.STACS.2026.64; read as arXiv:2601.04902v1, <https://arxiv.org/abs/2601.04902v1>: Theorems 13 and 15 in Section 3 (Monitor owns the condition), Theorem 16 in Section 5 (Timer owns the condition) and Theorem 23 in Section 6 (Church synthesis for Timer as Owner and Monitor as Agent, with the 1-resetting automata defined in Section 6), and Table 2 (summary), the definitions of timed games, strategies, controllers and the two synthesis problems in Section 2, and the abstract and introduction (the four reductions, the data setting), in the numbering of that version.
