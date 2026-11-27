# Min-entropy chain rule for conditioning on a variable with few values

Let $(L, A)$ be jointly distributed with $L$ taking at most $|\mathcal{L}|$ values in a finite set $\mathcal{L}$, let $f$ be any function of $A$ and $\delta > 0$. Then with probability at least $1 - \delta$ over $\ell \sim L$,

$$
H_\infty\bigl(f(A) \mid L = \ell\bigr) \ge H_\infty(f(A)) - \log_2|\mathcal{L}| - \log_2(1/\delta).
$$

## Proof sketch

For an outcome $v$, $\Pr[f(A)=v \mid L=\ell] \le \Pr[f(A)=v]/\Pr[L=\ell] \le 2^{-H_\infty(f(A))}/\Pr[L=\ell]$. The observations with $\Pr[L = \ell] < \delta/|\mathcal{L}|$ number at most $|\mathcal{L}|$, so they have total probability below $\delta$, and every other observation satisfies the bound.

Derived refinements (not stated in the cited sources):

- Pointwise form. The argument shows the bound for every single observation $\ell$ with $\Pr[L = \ell] \ge \delta/|\mathcal{L}|$, and that the remaining observations have total probability at most $\delta$.
- A map injective on the support of a distribution does not decrease its min-entropy.
- Uniform lifting. If $f(A)$ is $\gamma$-close to uniform on a finite set $\beta$ with $\gamma < 1$, there is $A'$ within distance $\gamma$ of $A$ with $H_\infty(f(A')) \ge \log_2|\beta| + \log_2(1-\gamma)$: cap the masses of $f(A)$ at $1/|\beta|$ and renormalize; the removed mass is at most $\gamma$, so the normalizer is at least $1-\gamma$, the new law stays within $\gamma$ and on the support of $f(A)$, and it is pulled back through the conditional laws of $A$ given $f(A)$.

## Depends on

- [k-sources, (k, ε)-sources and flat sources](weak-random-sources.md)
- [Conditional guessing probability and min-entropy](../../../ComputerScience/cryptography/randomness-extraction/conditional-guessing-probability-and-min-entropy.md)

## Sources

- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1–3), 1–336, 2012 (author's copy), Lemma 6.30 (chain rule for min-entropy: if $(W, X)$ is a $k$-source and $|\mathrm{Supp}(W)| \le 2^\ell$, then with probability at least $1-\varepsilon$ over $w \leftarrow W$, $X|_{W=w}$ is a $(k - \ell - \log(1/\varepsilon))$-source).
- E. Chattopadhyay, V. Goyal and X. Li, "Non-Malleable Extractors and Codes, with their Many Tampered Extensions", Proceedings of the 48th ACM Symposium on Theory of Computing (STOC 2016), numbering of arXiv:1505.00107v1, Lemma 3.11 (attributed there to Maurer–Wolf 1997: $\Pr_{y \sim Y}[H_\infty(X|Y = y) \ge H_\infty(X) - \log \ell - \log(1/\epsilon)] > 1 - \epsilon$ when $Y$ takes $\ell$ values).
- Y. Dodis, R. Ostrovsky, L. Reyzin and A. Smith, "Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data", SIAM Journal on Computing 38(1), 97–139, 2008, Lemma 2.2 (the averaged form).
