# Conditional distributions of computable random variables need not be computable

There is a pair of computable random variables in the unit interval whose conditional distribution, of the first given the second, has a version continuous on a set of measure one but is not computable on any set of measure one; it encodes the halting problem.

**Setting.** Random variables are measurable functions on the space $\{0,1\}^{\mathbb{N}}$ of infinite binary sequences with the product $\Pr$ of fair coin measures. For a computable Polish space $S$, a random variable $\mathsf{X}$ in $S$ is *$\Pr$-almost computable* if it is computable, as a function from $\{0,1\}^{\mathbb{N}}$ to $S$, on a set of $\Pr$-measure one: some program with oracle access to the input sequence $\varpi$ outputs a representation of $\mathsf{X}(\varpi)$ for $\Pr$-almost every $\varpi$. For a measure $\mu$, a function is *$\mu$-almost continuous* (*$\mu$-almost computable*) if it is continuous (computable) on a set of $\mu$-measure one. For random variables $\mathsf{Y}$ and $\mathsf{W}$ in $[0,1]$, a *conditional distribution map* of $\mathsf{Y}$ given $\mathsf{W}$ is a measurable map $x \mapsto \Pr[\mathsf{Y} \mid \mathsf{W} = x]$ from $[0,1]$ to the space of Borel probability measures on $[0,1]$, with the weak topology, that composed with $\mathsf{W}$ gives a regular version of the conditional distribution of $\mathsf{Y}$ given $\mathsf{W}$; such maps are defined up to sets of $\Pr_{\mathsf{W}}$-measure zero, where $\Pr_{\mathsf{W}}$ is the distribution of $\mathsf{W}$.

**Theorem (Ackerman, Freer and Roy).** There are $\Pr$-almost computable random variables $\mathsf{W}$ and $\mathsf{Y}$ in $[0,1]$ such that the conditional distribution map $\Pr[\mathsf{Y} \mid \mathsf{W} = \cdot\,]$ is $\Pr_{\mathsf{W}}$-almost continuous but not $\Pr_{\mathsf{W}}$-almost computable.

So the joint distribution of $(\mathsf{W}, \mathsf{Y})$ is computable while no version of the conditional distribution map is computable on a set of measure one. The same paper strengthens this to random variables whose conditional distribution map has an everywhere continuous version with infinitely differentiable conditional probability maps, still not $\Pr_{\mathsf{W}}$-almost computable, and shows that conditioning is computable when the observation is corrupted by independent computable noise with a sufficiently smooth bounded density.

## Depends on

- [Probability measure](../../../Probability/foundations/probability-measures/is-probability-measure.md)
- [Regular conditional distribution (kernel form)](../../../Probability/foundations/regular-conditional-distributions/is-regular-conditional-distribution.md)

## Proof depends on

- [Halting is undecidable](../halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The construction encodes the halting times of all Turing machines into the conditional distribution while keeping the joint distribution computable. An auxiliary pair $(\mathsf{X}, \mathsf{N})$, with $\mathsf{N}$ a natural number, is built so that the conditional probabilities $\Pr[\mathsf{N} = n \mid \mathsf{X} = x]$ are continuous almost everywhere, yet from them one could compute, for each machine, whether it halts. Taking $\mathsf{Y}$ uniform on $[0,1]$ and $\mathsf{M} = \lfloor -\log_2 \mathsf{Y} \rfloor$ geometric with parameter $\tfrac12$, the variable $\mathsf{W}$ is chosen with $\Pr[\mathsf{W} \mid \mathsf{Y}] = \Pr[\mathsf{X} \mid \mathsf{N} = \mathsf{M}]$, so that $\Pr[\mathsf{Y} \in (2^{-n-1}, 2^{-n}) \mid \mathsf{W} = x] = \Pr[\mathsf{N} = n \mid \mathsf{X} = x]$. An almost computable conditional distribution map would therefore decide the halting problem.

## Sources

- N. L. Ackerman, C. E. Freer and D. M. Roy, "On the computability of conditional probability", *Journal of the ACM* 66(3), Article 23, 2019, pp. 1–40, doi:10.1145/3321699; read as arXiv:1005.3014v4, <https://arxiv.org/abs/1005.3014v4>: Theorem 7.6 in Section 7 ("Noncomputable Almost-Continuous Conditional Distributions") with its proof, the definitions of Section 2 (almost computable random variables and functions) and of Section 3 (conditional distribution maps), and Section 8 (everywhere continuous versions), in that version.
