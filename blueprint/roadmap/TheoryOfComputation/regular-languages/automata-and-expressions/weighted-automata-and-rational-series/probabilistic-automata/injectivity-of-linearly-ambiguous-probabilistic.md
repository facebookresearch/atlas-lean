# Injectivity of linearly ambiguous four-state probabilistic automata is undecidable

No algorithm decides whether a given probabilistic automaton with four states, of linear ambiguity, assigns different acceptance probabilities to all distinct words.

**Theorem.** For a probabilistic finite automaton $\mathcal A = (x, \{M_a : a \in \Sigma\}, y)$ with acceptance probabilities $f_{\mathcal A}(w) = x^{\mathsf T} M_{w_1} \cdots M_{w_k} y$ (an initial distribution $x$, a final vector $y \in \{0,1\}^n$ and row-stochastic matrices $M_a$, a variant of [probabilistic automata](../probabilistic-automata-and-cut-point-languages.md)), the *injectivity problem* asks whether $f_{\mathcal A}$ is injective on $\Sigma^*$, that is, whether no two distinct words have the same acceptance probability. The injectivity problem for linearly ambiguous probabilistic finite automata with four states is undecidable; here *linearly ambiguous* means that the number of accepting paths of the underlying nondeterministic automaton on a word of length $m$ is bounded by a polynomial of degree $1$ in $m$.

For three-state linearly ambiguous PFA over letter monotonic languages the problem is NP-hard (Theorem 3 of the source); its decidability there is open.

## Depends on

- [Probabilistic automata and cut-point languages](../probabilistic-automata-and-cut-point-languages.md)
- [Stochastic matrix](../../../../../Probability/markov-chains/kolmogorov-s-criterion-for-reversibility/stochastic-matrix.md)

## Proof depends on

None.

## Expansion

The proof reduces the mixed modification Post correspondence problem, undecidable for alphabets of at least nine letters (Theorem 8 of the source): given morphisms $h, g$, is there a word $x_1 \cdots x_k$ and a choice $h_i, g_i \in \{h, g\}$, not all equal, with $h_1(x_1) \cdots h_k(x_k) = g_1(x_1) \cdots g_k(x_k)$? Words are encoded as numbers in a base, and a four-state PFA with upper-triangular structure, hence linearly ambiguous, assigns to an input a probability determined by the encoded pair of images, so that two distinct inputs have the same acceptance probability iff the instance has a solution.

## Sources

- P. C. Bell, "Polynomially ambiguous probabilistic automata on restricted languages", *Journal of Computer and System Sciences* 127:53–65, 2022, doi:[10.1016/j.jcss.2022.02.002](https://doi.org/10.1016/j.jcss.2022.02.002); read as arXiv:1902.09407v3, whose numbering is used here: Section 2 (injectivity, ambiguity), Theorem 8, Theorem 2 with its proof, and Theorem 3.
