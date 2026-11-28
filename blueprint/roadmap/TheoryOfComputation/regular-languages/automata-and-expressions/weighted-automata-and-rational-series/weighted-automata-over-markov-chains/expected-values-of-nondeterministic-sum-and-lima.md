# Expected values of nondeterministic Sum- and LimAvg-automata are uncomputable

No algorithm computes, in any representation of numbers with decidable equality, the expected value of a nondeterministic
Sum-automaton or LimAvg-automaton over a Markov chain, nor the distribution of a Sum-automaton, even when the probability measure
is uniform.

Let $\mathcal{A}$ range over nondeterministic [weighted automata evaluated over Markov chains](weighted-automata-evaluated-over-markov-chains.md).

**Theorem.**

1. The expected value and the distribution of nondeterministic Sum-automata are uncomputable, even for the uniform probability
   measure.
2. The expected value of nondeterministic LimAvg-automata, and the value of almost all words when it exists, are uncomputable,
   even for the uniform probability measure.

*Uncomputable* means that no Turing machine computes the quantity in any representation of numbers in which equality of two
represented numbers is decidable (the value $+\infty$ included). The proof (Theorem 7 of the source) is a Turing reduction from the quantitative universality problem for Sum-automata with weights $-1, 0, 1$ (is $\mathcal{A}(w) \le 0$ for every word $w$?); for the distribution it uses the threshold $\lambda = 0$. The source thus rules out exact computation even through representations of irrational numbers;
for LimAvg-automata it gives approximation algorithms in exponential time instead.

## Depends on

- [Weighted automata evaluated over Markov chains](weighted-automata-evaluated-over-markov-chains.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof is a Turing reduction from the quantitative universality problem for Sum-automata with weights $-1$, $0$ and $1$, whether
$\mathcal{A}(w) \le 0$ for every word $w$, which is undecidable (Krob; Almagor, Boker and Kupferman). Under the uniform measure every
finite word has positive probability, so $\mathcal{A}$ is universal exactly when $\mathbb{D}_{\mathcal{A}}(0) = 1$. For the expected
value, build $\mathcal{A}'$ with $\mathcal{A}'(w) = \min(\mathcal{A}(w), 0)$; then $\mathcal{A}$ is universal exactly when
$\mathbb{E}(\mathcal{A}) = \mathbb{E}(\mathcal{A}')$. For LimAvg, connect the accepting states of $\mathcal{A}$ and $\mathcal{A}'$ back to
their initial states by weight-$0$ transitions on a new letter; almost every infinite word then has value $\mathbb{E}(\mathcal{A})$,
respectively $\mathbb{E}(\mathcal{A}')$, and the same comparison applies.

## Sources

- J. Michaliszyn and J. Otop, "Non-deterministic weighted automata evaluated over Markov chains", *Journal of Computer and System Sciences* 108:118–136, 2020, doi:10.1016/j.jcss.2019.10.001; Section 4 of the version arXiv:1908.04625v2 (The exact value problems): Theorem 7 with its proof, and Section 6 (exponential-time approximation of LimAvg-automata).
