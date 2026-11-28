# Timed synthesis with an unbounded number of controller clocks is undecidable

In timed games where the environment plays timed actions and the controller answers immediately, no algorithm decides whether the controller has a winning strategy implemented by a deterministic timed automaton with some number of clocks, already for two-clock nondeterministic winning conditions; with the number of clocks fixed the problem is decidable.

Let $A,B$ be finite alphabets and $W\subseteq(A\cdot B\cdot\mathbb R_{\ge0})^\omega$ a language of timed $\omega$-words given by a nondeterministic timed automaton, possibly with $\varepsilon$-steps (see [timed Büchi automata](../timed-buchi-automata.md)). In the *timed synthesis game*, at each round Player I chooses a timed action $(a_i,t_i)$ and Player II replies immediately with an untimed action $b_i$; Player I wins iff the infinite play $a_1b_1t_1a_2b_2t_2\cdots$ lies in $W$. A *$k,m$-controller* for Player II is a deterministic timed automaton with $k$ clocks and maximal constant $m$ that reads Player I's actions and outputs Player II's replies. The *$k,m$-*, *$k$-* and plain *timed synthesis problems* ask whether Player II has a winning $k,m$-controller, a winning $k$-controller for some $m$, and a winning controller for some $k$ and $m$.

**Theorem (Piórkowski).** The timed synthesis problem is undecidable, already when Player I's winning condition $W$ is recognized by a nondeterministic timed automaton with two clocks (Piórkowski, 2022, as stated in the introduction of Lasota, Lehaut, Parreaux and Piórkowski, STACS 2026).

For one-clock winning conditions the same introduction records the problem as open before that paper, whose Theorem 23 settles it only for a 1-resetting extension of one-clock automata used for both the winning condition and the controllers (see [one-clock timed synthesis problems](one-clock-timed-synthesis-problems-are-undecid.md)); the plain one-clock case is open as far as these sources go. Theorem 6.1 of Clemente, Lasota and Piórkowski (ICALP 2020) is stated for one-clock conditions, and this page does not rely on that form.

For every fixed $k$, the $k$-timed synthesis problem (with $m$ synthesized) is decidable, and the source uses these games to show that deterministic separability of nondeterministic timed languages, by a deterministic timed automaton with $k$ clocks, is decidable, in contrast with the undecidability of deciding whether a nondeterministic timed language is deterministic.

## Depends on

- [Timed Büchi automata](../timed-buchi-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The two-clock proof is in Piórkowski's thesis, which reduces from a problem on lossy counter machines; the ICALP 2020 paper sketches such a reduction from the finiteness (boundedness) problem for lossy counter machines with four counters, undecidable by Mayr, in which Player I's moves spell strictly monotonic timed words encoding runs of the machine and the existence of a winning controller with some unspecified number of clocks encodes the finiteness question. A good expansion reads the two-clock proof in the thesis and links pages for the undecidable lossy-counter-machine problem it reduces from and for the encoding of runs by two-clock timed languages.

## Sources

- S. Lasota, M. Lehaut, J. Parreaux and R. Piórkowski, "One-Clock Synthesis Problems", in *43rd International Symposium on Theoretical Aspects of Computer Science (STACS 2026)*, LIPIcs 364, 2026, paper 64, doi:10.4230/LIPIcs.STACS.2026.64; read as arXiv:2601.04902v1: the introduction (the two-clock result of [31] and the one-clock case left open) and Theorem 23 in Section 6.
- R. Piórkowski, *Simplification problems for infinite-state systems*, PhD thesis, University of Warsaw, 2022 (cited after the paper above, its reference [31]).
- Lorenzo Clemente, Sławomir Lasota and Radosław Piórkowski, "Timed Games and Deterministic Separability", in *47th International Colloquium on Automata, Languages, and Programming (ICALP 2020)*, LIPIcs 168, 2020, pp. 121:1–121:16, doi:[10.4230/LIPIcs.ICALP.2020.121](https://doi.org/10.4230/LIPIcs.ICALP.2020.121); read in arXiv:2004.12868v1 ([arXiv](https://arxiv.org/abs/2004.12868v1)), whose numbering is used, for the game model and the decidability for a fixed number of clocks: the introduction (paragraph "Timed games", which refers to Theorem 6.1, and Theorems 1.1-1.3), Theorem 6.1 in Section 6, the section on timed synthesis games (games, controllers and the synthesis problems), and Appendix C ("Undecidability of timed synthesis for 1-NTA conditions") with the proof of Theorem 6.1.
