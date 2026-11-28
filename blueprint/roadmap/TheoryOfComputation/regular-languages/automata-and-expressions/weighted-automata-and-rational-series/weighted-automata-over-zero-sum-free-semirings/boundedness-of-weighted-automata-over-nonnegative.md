# Boundedness of weighted automata over the nonnegative rationals is undecidable

No algorithm decides whether a weighted automaton with nonnegative rational weights has bounded values; zero isolation, whether its values stay above some positive constant, is undecidable as well.

Consider [weighted automata](../weighted-automata-over-a-semiring.md) over the semiring $(\mathbb Q_{\ge0},+,\cdot)$, each defining a function $\mathcal A:\Sigma^*\to\mathbb Q_{\ge0}$. An instance is a finite alphabet, a finite set of states and the initial, transition and final weights, each a nonnegative rational given as a fraction of integers; in the threshold problems the threshold $c$ is a nonnegative rational given the same way.

**Theorem.** The following problems are undecidable for weighted automata over $(\mathbb Q_{\ge0},+,\cdot)$:
1. (*boundedness*) is there a number $c$ with $\mathcal A(w)\le c$ for all $w\in\Sigma^*$?
2. (*zero isolation*) is there a rational $c>0$ with $\mathcal A(w)\ge c$ for all $w\in\Sigma^*$?
3. the $\le$-threshold and $\ge$-threshold problems: given $\mathcal A$ and $c$, is $\mathcal A(w)\le c$ (respectively $\ge c$) for all $w$?

The threshold problems remain undecidable for linearly ambiguous automata. For finitely ambiguous automata, boundedness and the $\le$-threshold problem are decidable, and zero isolation and the $\ge$-threshold problem are decidable assuming Schanuel's conjecture; for copyless linear cost register automata boundedness is decidable in polynomial time (all from the source).

## Depends on

- [Weighted automata over a semiring](../weighted-automata-over-a-semiring.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../emptiness-problem-for-probabilistic-automata.md)
- [The value-1 problem for probabilistic automata is undecidable](../value-1-problem-for-probabilistic-automata.md)

## Expansion

The threshold problems and zero isolation come from probabilistic automata, which are weighted automata over $\mathbb Q_{\ge0}$: thresholds by Paz, and zero isolation by Gimbert and Oualhadj, as the source recalls. Boundedness is reduced from the $\le\frac12$ threshold problem for probabilistic automata: given $\mathcal A$, build over $\Sigma\cup\{\#\}$ an automaton $\mathcal B$ with $\mathcal B(w_1\#\cdots\#w_n)=2\mathcal A(w_1)\cdots2\mathcal A(w_n)$, the fresh letter $\#$ restarting $\mathcal A$. Then $\mathcal B$ is bounded iff $\mathcal A(w)\le\frac12$ for every word, since a single word with $\mathcal A(w)>\frac12$ makes $\mathcal B((w\#)^n)$ grow exponentially. The source notes it found this argument for boundedness nowhere in the literature (a similar one is in Blondel and Tsitsiklis).

## Sources

- Wojciech Czerwiński, Engel Lefaucheux, Filip Mazowiecki, David Purser and Markus A. Whiteland, "The boundedness and zero isolation problems for weighted automata over nonnegative rationals", in *Proceedings of the 37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, pp. 1–13, doi:[10.1145/3531130.3533336](https://doi.org/10.1145/3531130.3533336); read in arXiv:2205.13516v1 ([arXiv](https://arxiv.org/abs/2205.13516v1)), whose numbering is used: Section 3 (Detailed state of the art and our results): Corollary 3.1 with the argument before it, Proposition 3.2 (finitely ambiguous automata) and Theorem 3.3 (copyless linear cost register automata).
