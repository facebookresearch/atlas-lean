# Deterministic membership of one-clock timed automata is undecidable

No algorithm decides whether the timed language of a given one-clock nondeterministic timed automaton without silent transitions is recognized by some deterministic timed automaton.

The theorem is stated in the source's model (Section 5), which differs from the [timed automata over finite timed words](timed-automata-over-finite-timed-words.md) of this folder: a timed word is a finite sequence $(\sigma_1, t_1) \cdots (\sigma_n, t_n)$ with $0 \le t_1 \le \cdots \le t_n$ (equal timestamps allowed); clock constraints are Boolean combinations of $x_i \sim z$ and $x_i - x_j \sim z$ with $z \in \mathbb{Z}$ and ${\sim} \in \{=, <, \le, >, \ge\}$; and a timed automaton is *deterministic* if it has one initial location and any two rules with the same source location and letter and jointly satisfiable constraints have the same reset set and target. The source does not transfer the result to other models.

**Theorem.** Let $A$ range over nondeterministic timed automata in this model with one clock and no $\varepsilon$-transitions. The following problems are undecidable:
1. (DTA membership) is $L(A)$ recognized by some deterministic timed automaton, with any number of clocks?
2. ($m$-DTA membership, for each fixed $m>0$) is $L(A)$ recognized by some deterministic timed automaton whose constants are at most $m$ in absolute value, with any number of clocks?

This strengthens the undecidability of DTA membership for timed automata with two clocks (Finkel, Theorem 1), and holds although universality of one-clock timed automata is decidable. When the number $k$ of clocks of the deterministic automaton is fixed (and, optionally, its maximal constant), membership is decidable for one-clock inputs without $\varepsilon$-transitions (Theorem 1.1 of the source), but undecidable for two-clock inputs and for one-clock inputs with $\varepsilon$-transitions (Theorem 1.5 of the source).

## Depends on

- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

As for register automata, the proof reduces the finiteness problem for lossy counter machines with $4$ counters (Mayr). A counter valuation $u$ is written $c_1^{u(c_1)}\cdots c_4^{u(c_4)}$, and a run $(p_0,u_0)\to\cdots\to(p_n,u_n)$ is encoded backwards as the timed word $p_n\delta_nu_n\cdots p_1\delta_1u_1\,p_0u_0$, consecutive configurations one time unit apart and every surviving unit of a counter matched with an occurrence exactly one time unit later. Read backwards, counters may only grow spontaneously, so the only error to detect is a unit without a match one time unit later, which a one-clock automaton without $\varepsilon$-transitions can guess; $A$ accepts the timed words that are not reversal encodings. If the machine reaches finitely many configurations, of size at most $k$, the encodings are recognized by a deterministic automaton with $k+1$ clocks, hence so is their complement $L(A)$. Otherwise a deterministic automaton with $k$ clocks reading the encoding of a run with a counter above $k$ must forget a time stamp $t$, and perturbing its partner at $t+1$ produces a non-encoding that it still treats as an encoding.

## Sources

- Lorenzo Clemente, Sławomir Lasota and Radosław Piórkowski, "Determinisability of register and timed automata", *Logical Methods in Computer Science* 18(2), 2022, paper 9, doi:[10.46298/lmcs-18(2:9)2022](https://doi.org/10.46298/lmcs-18(2:9)2022); numbering of arXiv:2104.03690v4 ([arXiv](https://arxiv.org/abs/2104.03690v4)): Theorem 1.3 (Section 1.3) and its proof in Section 8.3 (Lemma 8.5); Theorems 1.1 and 1.5; the timed words, clock constraints and deterministic timed automata of Section 5.
- Olivier Finkel, "Undecidable Problems About Timed Automata", in *Formal Modeling and Analysis of Timed Systems (FORMATS 2006)*, Lecture Notes in Computer Science 4202, Springer, 2006, pp. 187–199, doi:[10.1007/11867340_14](https://doi.org/10.1007/11867340_14); numbering of arXiv:0712.1363v1 ([arXiv](https://arxiv.org/abs/0712.1363v1)): Theorem 1 (determinizability, the result improved).
