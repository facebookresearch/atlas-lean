# Timed synthesis with an unbounded number of controller clocks is undecidable

In timed games where the environment plays timed actions and the controller answers immediately, no algorithm decides whether the controller has a winning strategy implemented by a deterministic timed automaton with some number of clocks, even for one-clock nondeterministic winning conditions; with the number of clocks fixed the problem is decidable.

Let $A,B$ be finite alphabets and $W\subseteq(A\cdot B\cdot\mathbb R_{\ge0})^\omega$ a language of timed $\omega$-words given by a nondeterministic timed automaton, possibly with $\varepsilon$-steps (see [timed Büchi automata](../timed-buchi-automata.md)). In the *timed synthesis game*, at each round Player I chooses a timed action $(a_i,t_i)$ and Player II replies immediately with an untimed action $b_i$; Player I wins iff the infinite play $a_1b_1t_1a_2b_2t_2\cdots$ lies in $W$. A *$k,m$-controller* for Player II is a deterministic timed automaton with $k$ clocks and maximal constant $m$ that reads Player I's actions and outputs Player II's replies. The *$k,m$-*, *$k$-* and plain *timed synthesis problems* ask whether Player II has a winning $k,m$-controller, a winning $k$-controller for some $m$, and a winning controller for some $k$ and $m$.

**Theorem.** The timed synthesis problem is undecidable, already when Player I's winning condition $W$ is recognized by a nondeterministic timed automaton with one clock (Theorem 6.1 of the source).

For every fixed $k$, the $k$-timed synthesis problem (with $m$ synthesized) is decidable, and the source uses these games to show that deterministic separability of nondeterministic timed languages, by a deterministic timed automaton with $k$ clocks, is decidable, in contrast with the undecidability of deciding whether a nondeterministic timed language is deterministic.

## Depends on

- [Timed Büchi automata](../timed-buchi-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from the finiteness problem for lossy counter machines with four counters, undecidable by Mayr: Player I's moves spell strictly monotonic timed words encoding runs of the machine, a configuration $(p,u)$ being written as $p\,c_1^{n_1}c_2^{n_2}c_3^{n_3}c_4^{n_4}$ with the timing used to relate consecutive configurations, and the winning condition of Player I is a one-clock nondeterministic timed language built from the machine. The existence of a winning controller, with some unspecified number of clocks, then encodes the finiteness question for the machine; for each fixed number of clocks the problem remains decidable.

## Sources

- Lorenzo Clemente, Sławomir Lasota and Radosław Piórkowski, "Timed Games and Deterministic Separability", in *47th International Colloquium on Automata, Languages, and Programming (ICALP 2020)*, LIPIcs 168, 2020, pp. 121:1–121:16, doi:[10.4230/LIPIcs.ICALP.2020.121](https://doi.org/10.4230/LIPIcs.ICALP.2020.121); read in arXiv:2004.12868v1 ([arXiv](https://arxiv.org/abs/2004.12868v1)), whose numbering is used: the introduction (paragraph "Timed games" and Theorem 6.1 stated there, with Theorems 1.1-1.3), the section on timed synthesis games (games, controllers and the synthesis problems), and the appendix section "Undecidability of timed synthesis for 1-NTA conditions" with the proof of Theorem 6.1.
