# Clock minimization of timed automata is undecidable

For every $n \ge 2$, no algorithm decides whether a given timed automaton with $n$ clocks is equivalent to one with $n - 1$
clocks.

Fix an integer $n \ge 2$. The following problem is undecidable: given a
[timed automaton over finite timed words](timed-automata-over-finite-timed-words.md) $\mathcal{A}$ with $n$ clocks, is there a
timed automaton $\mathcal{B}$ with $n - 1$ clocks such that $L(\mathcal{B}) = L(\mathcal{A})$? Here $n$ is fixed; only the
automaton varies, and no witness $\mathcal{B}$ has to be constructed. Tripakis had shown that no algorithm decides the question
and also constructs such a witness.

The method does not apply to $n = 1$: universality of timed automata with one clock is decidable (Ouaknine and Worrell), and
it is decidable whether a timed automaton with one clock is equivalent to one without clocks. For timed Büchi automata the
source states the analogous problem, for $n \ge 2$, to be $\Pi^1_1$-hard.

## Depends on

- [Timed automata over finite timed words](timed-automata-over-finite-timed-words.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the universality problem for timed automata with $n$ clocks, undecidable for $n \ge 2$. Let $A_n$ be the
timed language of the timed words $t_1 . a \cdots t_k . a$ with $n$ pairs of occurrences of $a$ exactly one time unit apart;
$A_n$ is timed regular but is not accepted by any timed automaton with fewer than $n$ clocks (Henzinger, Kopke and Wong-Toi).
Given $L = L(\mathcal{A})$ with at most $n$ clocks and a new letter $c$, the union $\mathcal{V}_n$ of
$L . (\mathcal{R} \times \{c\}) . (\mathcal{R} \times \Sigma)^\star$, the timed words with no $c$ or at least two $c$'s, and
$(\mathcal{R} \times \Sigma)^\star . (\mathcal{R} \times \{c\}) . A_n$ is accepted with $n$ clocks. If $L$ is universal,
$\mathcal{V}_n$ is accepted without clocks; if some $u \notin L$, then $u . 1 . c . x \in \mathcal{V}_n$ exactly when
$x \in A_n$, and an automaton with $n - 1$ clocks cannot recognize $A_n$ from the finitely many global states it can reach
after $u . 1 . c$.

## Sources

- O. Finkel, "Undecidable problems about timed automata", in *Formal Modeling and Analysis of Timed Systems (FORMATS 2006)*, Lecture Notes in Computer Science 4202, pp. 187–199, Springer, 2006, doi:10.1007/11867340_14; Theorem 2 of the version arXiv:0712.1363v1 with its proof, Remark 3 (the case of one clock), and Theorem 10 (timed Büchi automata).
