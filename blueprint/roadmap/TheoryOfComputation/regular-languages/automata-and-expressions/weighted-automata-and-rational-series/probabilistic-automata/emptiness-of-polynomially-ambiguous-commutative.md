# Emptiness of polynomially ambiguous commutative probabilistic automata is undecidable

The cut-point emptiness problem for probabilistic automata stays undecidable when all transition matrices commute and the automaton is only polynomially ambiguous, and hence when inputs are restricted to a letter monotonic language $a_1^* a_2^* \cdots a_k^*$.

**Theorem.** A *probabilistic finite automaton* (PFA) with $n$ states over an alphabet $\Sigma$ is $\mathcal A = (x, \{M_a : a \in \Sigma\}, y)$ with an initial distribution $x \in \mathbb R^n$, a final vector $y \in \{0, 1\}^n$ and row-stochastic matrices $M_a \in \mathbb R^{n \times n}$; the acceptance probability of $w = w_1 \cdots w_k$ is $f_{\mathcal A}(w) = x^{\mathsf T} M_{w_1} \cdots M_{w_k} y$. It is *commutative* if all $M_a$ commute. Its degree of ambiguity is that of the nondeterministic automaton with an $a$-edge from $i$ to $j$ whenever $(M_a)_{ij} > 0$, and it is *polynomially ambiguous* if the number of accepting paths of this automaton on words of length $m$ is bounded by a polynomial in $m$. For $\lambda \in [0, 1]$, the *emptiness problem* asks whether $\{w : f_{\mathcal A}(w) \ge \lambda\} = \emptyset$, and the *strict emptiness problem* whether $\{w : f_{\mathcal A}(w) > \lambda\} = \emptyset$. Then:

1. both problems are undecidable for polynomially ambiguous commutative PFA (with rational entries), and therefore for PFA whose inputs are restricted to letter monotonic languages $L \subseteq a_1^* \cdots a_m^*$;
2. both problems remain undecidable for polynomially ambiguous PFA over a binary alphabet whose inputs are restricted to a bounded language $L \subseteq w_1^* \cdots w_m^*$.

For general PFA, emptiness is the classical undecidable [emptiness problem for probabilistic automata](../emptiness-problem-for-probabilistic-automata.md). The Post correspondence problem, the usual source of such reductions, is decidable over letter monotonic languages, and commuting matrices make many matrix problems decidable, which is why the reduction goes through Hilbert's tenth problem instead.

## Depends on

- [Probabilistic automata and cut-point languages](../probabilistic-automata-and-cut-point-languages.md)
- [Stochastic matrix](../../../../../Probability/markov-chains/kolmogorov-s-criterion-for-reversibility/stochastic-matrix.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof reduces Hilbert's tenth problem: whether an integer polynomial $P(n_1, \dots, n_k)$ has a zero is reduced to whether a $\mathbb Z$-rational formal power series vanishes on some word. Since the matrices commute, only the Parikh vector of the input matters, so a word over $\{a_1, \dots, a_k\}$ stands for the tuple of letter counts. The values of $P$ are encoded with upper-triangular matrices built from Kronecker products, which are polynomially ambiguous (Lemma 6), instead of Turakainen's general conversion of weighted to stochastic matrices, which would make every entry positive and the automaton exponentially ambiguous. Further encodings pass from non-strict to strict cut-points and to a binary alphabet.

## Sources

- P. C. Bell, "Polynomially ambiguous probabilistic automata on restricted languages", *Journal of Computer and System Sciences* 127:53–65, 2022, doi:[10.1016/j.jcss.2022.02.002](https://doi.org/10.1016/j.jcss.2022.02.002); read as arXiv:1902.09407v3, whose numbering is used here: Section 2 (PFA, cut-point languages, bounded and letter monotonic languages, ambiguity), Theorem 1 and its proof, Theorem 5 and Lemma 6.
