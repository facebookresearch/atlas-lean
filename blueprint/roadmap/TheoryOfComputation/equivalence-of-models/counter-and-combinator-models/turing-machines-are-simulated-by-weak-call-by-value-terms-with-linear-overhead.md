# Turing machines are simulated by weak call-by-value terms with linear overhead

Let $f : \Sigma^* \to \Sigma^*$ be computed by a deterministic single-tape Turing machine $\mathcal{M}$ in the model of Dal Lago and Accattoli, in time $T$ and space $S$. There is a term $\overline{\mathcal{M}}$ of the [weak call-by-value λ-calculus](weak-call-by-value-lambda-calculus-and-its-cost-measures.md) such that for every $x \in \Sigma^*$:

1. $\overline{\mathcal{M}}\,\ulcorner x \urcorner \succ^* \ulcorner f(x) \urcorner$, with $\ulcorner \cdot \urcorner$ the Scott encoding of strings;
2. $\|\overline{\mathcal{M}}\,\ulcorner x \urcorner\|_S \in O(|x| + S(|x|))$;
3. $\|\overline{\mathcal{M}}\,\ulcorner x \urcorner\|_T \in O(|x| + T(|x|))$.

The term is built in the deterministic λ-calculus, the fragment in which every argument is a value and every term has at most one weak redex, so all weak evaluation strategies, call-by-value included, take the same number of β-steps, bounded by $O(T(|x|) + |x|)$.

## Depends on

- [The weak call-by-value λ-calculus and its time and space measures](weak-call-by-value-lambda-calculus-and-its-cost-measures.md)
## Proof depends on

The machine encoding and one-transition simulation listed in Expansion are the missing prerequisites; multi-tape class definitions do not supply them.

## Expansion

This page becomes ready once:

- The deterministic single-tape machine model of Dal Lago and Accattoli, including tape alphabet, configurations, input/output representation and the time and space measures (statement prerequisite; not yet stated)
- The encoding of strings, tapes and configurations and the simulation of one machine transition by a constant number of β-steps (Dal Lago and Accattoli, Lemmas 5.1 to 5.3 and Corollary 5.4) (proof prerequisite; not yet stated)

## Sources

- Ugo Dal Lago and Beniamino Accattoli, "Encoding Turing Machines into the Deterministic Lambda-Calculus", arXiv:1711.10078, 2017: Section 2 (deterministic λ-calculus, Lemma 2.1) and Theorem 5.5 (linear simulation, $\Theta(g(|s|) + |s|)$ steps).
- Yannick Forster, Fabian Kunze and Marc Roth, "The Weak Call-By-Value λ-Calculus is Reasonable for Both Time and Space", POPL 2020; arXiv:1902.07515: Theorem 23 (time and space bounds 1 to 3 above, via Theorem 5.5 of the previous source).
