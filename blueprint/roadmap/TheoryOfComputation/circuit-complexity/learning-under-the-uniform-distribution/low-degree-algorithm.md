# The low-degree algorithm learns classes with small Fourier weight above degree t

Read Boolean values as signs $\pm1$ and let $\hat f(S)$ denote Fourier coefficients on $\{0,1\}^n$. Fix a degree $t$ and let $N_t = |\{S \subseteq [n] : |S| \le t\}| \le (n+1)^t$. The low-degree algorithm estimates each $\hat f(S)$ with $|S| \le t$ by the empirical average $\tilde c(S) = \frac1m\sum_j f(x_j)\chi_S(x_j)$ over $m$ uniform random examples and outputs the sign of $\sum_{|S|\le t}\tilde c(S)\chi_S$. If $\varepsilon, \delta > 0$,

$$
m \ge \frac{4N_t}{\varepsilon}\ln\frac{2N_t}{\delta},
$$

and every $f \in C$ satisfies $\sum_{|S| > t}\hat f(S)^2 \le \varepsilon/2$, then the algorithm learns $C$ from uniform random examples with error $\varepsilon$ and confidence $1 - \delta$.

## Proof sketch

Each estimate is an average of $m$ independent values in $[-1,1]$ with mean $\hat f(S)$, so by Hoeffding and a union bound all $N_t$ estimates are within $\gamma = \sqrt{\varepsilon/(2N_t)}$ except with probability $2N_t e^{-m\varepsilon/(4N_t)} \le \delta$. Rounding a real approximation $g$ to its sign misclassifies at most a $\mathbb{E}(f - g)^2$ fraction of points, and by Plancherel this is at most $N_t\gamma^2 + \sum_{|S|>t}\hat f(S)^2 \le \varepsilon$.

## Depends on

- [Learning from uniform random examples](learning-from-uniform-random-examples.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)
- [Rounding to the sign](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/spectral-structure-of-boolean-functions/bool-dist-le-expect-sq-sub.md)
- [Plancherel identity on the subsets of a finite set](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/fourier-plancherel.md)

## Sources

- Nathan Linial, Yishay Mansour and Noam Nisan, "Constant Depth Circuits, Fourier Transform, and Learnability", Journal of the ACM, 1993.
- Ryan O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
