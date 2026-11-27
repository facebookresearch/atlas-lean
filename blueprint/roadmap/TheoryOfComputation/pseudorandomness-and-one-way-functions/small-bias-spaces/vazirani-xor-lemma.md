# Vazirani's XOR lemma and almost k-wise independence of small-bias spaces

For every distribution $X$ on $\{0,1\}^n$, the statistical distance from the uniform distribution $U_n$ satisfies

$$
\Delta(X, U_n) \le \frac12 \Bigl(\sum_{\emptyset \ne S \subseteq [n]} \mathrm{bias}_X(S)^2\Bigr)^{1/2}.
$$

Consequently an $\varepsilon$-biased $X$ is within $\tfrac12\sqrt{2^n - 1}\,\varepsilon$ of uniform, and if $X$ is $k$-wise $\varepsilon$-biased then its marginal on any $k$ coordinates is within $\tfrac12\sqrt{2^k - 1}\,\varepsilon$ of uniform. Moreover (linear composition), if $c_1, \dots, c_m \in \mathbb{F}_2^n$ are $k$-wise linearly independent and $X$ is $\varepsilon$-biased, then $y_j = \langle c_j, x\rangle$ defines a $k$-wise $\varepsilon$-biased distribution on $\{0,1\}^m$.

## Proof sketch

Parseval gives $\sum_S \mathrm{bias}_X(S)^2 = 2^n \,\mathrm{cp}(X)$ for the collision probability, and Cauchy–Schwarz bounds the $\ell_1$ distance to uniform by $\sqrt{2^n\,\mathrm{cp}(X) - 1}$; the $S = \emptyset$ term contributes the $1$. Marginals on $T$ have the biases of $X$ at subsets of $T$. For linear composition, the bias of $y$ at $T$ is the bias of $x$ at the support of $\sum_{j \in T} c_j$, which is nonempty by independence.

## Depends on

- [Small-bias distribution and generator](../space-bounded-and-small-bias-generators/small-bias-distributions.md)
- [Parseval's identity on the Boolean cube](../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-parseval.md)
- [Total variation distance of functions on a finite set](../../../Probability/markov-chains/mixing-times-of-markov-chains/tv-dist.md)

## Sources

- U. V. Vazirani, "Randomness, Adversaries and Computation", PhD thesis, University of California, Berkeley, 1986.
- J. Naor and M. Naor, "Small-Bias Probability Spaces: Efficient Constructions and Applications", SIAM Journal on Computing 22(4), 838–856, 1993, Lemma 2 as restated by Alon–Goldreich–Håstad–Peralta (linear composition with a $k$-wise independent linear space).
- N. Alon, O. Goldreich, J. Håstad and R. Peralta, "Simple Constructions of Almost k-wise Independent Random Variables", Random Structures & Algorithms 3(3), 289–304, 1992, Lemma 1 and Corollary 1 (Vazirani's lemma: $L_1$ distance at most $(2^k-1)^{1/2}\varepsilon$ on $k$ coordinates).
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1–3), 2012, Section 8.2.
