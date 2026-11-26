# Pointwise min-entropy chain rule and uniform lifting

Let $J$ be a joint distribution of $(L, A)$ with $L$ in a finite set $\mathcal{L}$, let $f$ be any function of $A$ and $\delta > 0$. If an observation $\ell$ has $\Pr[L = \ell] \ge \delta/|\mathcal{L}|$, then

$$
H_\infty\bigl(f(A) \mid L = \ell\bigr) \ge H_\infty(f(A)) - \log_2|\mathcal{L}| - \log_2(1/\delta),
$$

and the observations with $\Pr[L = \ell] < \delta/|\mathcal{L}|$ have total probability at most $\delta$. Also, a map injective on the support of a distribution does not decrease its min-entropy, and (uniform lifting) if $f(A)$ is $\gamma$-close to uniform on a finite set $\beta$ with $\gamma < 1$, there is $A'$ within distance $\gamma$ of $A$ with $H_\infty(f(A')) \ge \log_2|\beta| + \log_2(1-\gamma)$.

## Proof sketch

For an outcome $v$, $\Pr[f(A)=v \mid L=\ell] \le \Pr[f(A)=v]/\Pr[L=\ell] \le 2^{-H_\infty}|\mathcal{L}|/\delta$. The light observations number at most $|\mathcal{L}|$, each of probability below $\delta/|\mathcal{L}|$. For lifting, cap the masses of $f(A)$ at $1/|\beta|$ and redistribute, pulling the change back through conditional laws of $A$ given $f(A)$.

## Depends on

- [k-sources, (k, ε)-sources and flat sources](weak-random-sources.md)
- [Conditional guessing probability and min-entropy](../../../ComputerScience/cryptography/randomness-extraction/conditional-guessing-probability-and-min-entropy.md)

## Sources

- Y. Dodis, R. Ostrovsky, L. Reyzin and A. Smith, "Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data", SIAM Journal on Computing, 2008.
