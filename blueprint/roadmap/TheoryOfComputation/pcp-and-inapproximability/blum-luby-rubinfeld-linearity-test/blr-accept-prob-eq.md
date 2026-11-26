# Acceptance probability of the BLR test in Fourier form

For $f : \{-1, 1\}^n \to \{-1, 1\}$,

$$\Pr_{x, y}\big[f(x) f(y) = f(x y)\big] = \frac12 + \frac12 \sum_{S} \hat f(S)^3.$$

The indicator of acceptance is $\tfrac12 + \tfrac12 f(x) f(y) f(x y)$, and
$\mathbb{E}_{x,y}[f(x) f(y) f(x y)] = \mathbb{E}_x[f(x)\,(f * f)(x)] = \sum_S \hat f(S)^3$ by
Plancherel and the convolution theorem.

## Sources

- Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), equation (1.10) in the proof of Theorem 1.30.
