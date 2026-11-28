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
- Yannick Forster, Fabian Kunze and Marc Roth, "The Weak Call-by-Value λ-Calculus Is Reasonable for Both Time and Space", Proceedings of the ACM on Programming Languages 4 (POPL), Article 27, 2020: Section 5 and Theorem 5.1 (time and space bounds 1 to 3 above, proved by taking the term of Theorem 5.5 of the previous source; Theorem 23 of arXiv:1902.07515v1).
- Beniamino Accattoli and Ugo Dal Lago, "On the Invariance of the Unitary Cost Model for Head Reduction", 23rd International Conference on Rewriting Techniques and Applications (RTA 2012), LIPIcs 15, pp. 22 to 37, 2012: Section 6 and Theorem 6.1 (Invariance, Part II), the published form of the encoding with Scott-encoded strings and $O(g(|u|) + |u|)$ steps, stated there for head reduction. The weak-strategy independence used here comes from the deterministic λ-calculus of the first source.
- Ugo Dal Lago and Simone Martini, "On Constructor Rewrite Systems and the Lambda Calculus", Logical Methods in Computer Science 8(3:12), 2012: Theorem 4.17 (a Turing machine computing $f$ in time $g$ is simulated by a λ-term normalizing $\ulcorner v \urcorner$ to $\ulcorner f(v) \urcorner$ in $O(g(|v|))$ weak call-by-value β-steps, with that paper's own string encoding); a published locator for the time bound of item 3 only.
