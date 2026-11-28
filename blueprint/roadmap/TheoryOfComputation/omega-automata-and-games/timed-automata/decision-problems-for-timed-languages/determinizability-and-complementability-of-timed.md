# Determinizability and complementability of timed automata are undecidable

No algorithm decides whether a given timed automaton is equivalent to a deterministic one, and none decides whether the
complement of its timed language is timed regular.

Let $\mathcal{A}$ range over [timed automata over finite timed words](timed-automata-over-finite-timed-words.md). Each of the
following two problems is undecidable:

1. given $\mathcal{A}$, is $L(\mathcal{A})$ accepted by some deterministic timed automaton?
2. given $\mathcal{A}$, is the complement $L(\mathcal{A})^c$ accepted by some timed automaton?

The bounded-resource versions are undecidable as well: given $\mathcal{A}$ and integers $n, K \ge 0$, it is undecidable
whether some $\mathcal{B} \in TA(n, K)$ satisfies $L(\mathcal{B})^c = L(\mathcal{A})$, and whether some deterministic
$\mathcal{B} \in TA(n, K)$ satisfies $L(\mathcal{B}) = L(\mathcal{A})$, even when no witness $\mathcal{B}$ has to be
constructed. Tripakis had shown that no algorithm decides these questions and also constructs such a witness.

For timed Büchi automata on infinite timed words the analogous problems are
[Π¹₁-hard](for-timed-buchi-automata-determinizability-and-c.md).

## Depends on

- [Timed automata over finite timed words](timed-automata-over-finite-timed-words.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the universality problem for timed automata over finite timed words, which Alur and Dill proved
undecidable. Let $A$ be the timed regular language of the timed words $t_1 . a \cdots t_n . a$ in which some two occurrences
of $a$ are exactly one time unit apart; its complement is not timed regular. Given $L = L(\mathcal{A})$ over $\Sigma$ and a new
letter $c$, let $\mathcal{L}$ be the union of $L . (\mathcal{R} \times \{c\}) . (\mathcal{R} \times \Sigma)^\star$, the timed
words with no $c$ or at least two $c$'s, and $(\mathcal{R} \times \Sigma)^\star . (\mathcal{R} \times \{c\}) . A$. If $L$ is
universal, $\mathcal{L}$ is the set of all timed words over $\Sigma \cup \{c\}$, which a deterministic automaton without clocks
accepts, and so does its empty complement. If some $u \notin L$, then $u . 1 . c . x \in \mathcal{L}$ exactly when $x \in A$,
so $\mathcal{L}^c$ is not timed regular, and $\mathcal{L}$ is not deterministic because deterministic timed languages are closed
under complement. Since the clock-free witnesses in the first case lie in $TA(0, 0)$, the same reduction handles the
bounded-resource versions.

## Sources

- O. Finkel, "Undecidable problems about timed automata", in *Formal Modeling and Analysis of Timed Systems (FORMATS 2006)*, Lecture Notes in Computer Science 4202, pp. 187–199, Springer, 2006, doi:10.1007/11867340_14; Theorem 1 of the version arXiv:0712.1363v1 with its proof, and the paragraph after it on Tripakis's Problems 10 and 11.
