# Blum–Luby–Rubinfeld linearity test

Let $f : \{-1, 1\}^n \to \{-1, 1\}$ (a function $\mathbb{F}_2^n \to \mathbb{F}_2$ in the $\pm 1$
encoding) and $\varepsilon \in \mathbb{R}$. If the BLR test accepts $f$ with probability at least
$1 - \varepsilon$, then $f$ is $\varepsilon$-close to a linear function: there is $S$ with
$\mathrm{dist}(f, \chi_S) \le \varepsilon$.

The proof bounds $\sum_S \hat f(S)^3 \le \max_S \hat f(S) \cdot \sum_S \hat f(S)^2 = \max_S \hat f(S)$
(Parseval) and compares with the distance formula
$\mathrm{dist}(f, \chi_S) = \tfrac12 - \tfrac12 \hat f(S)$. The source states the theorem for
acceptance probability exactly $1 - \varepsilon$; the form with "at least" is equivalent.

## Sources

- Manuel Blum, Michael Luby and Ronitt Rubinfeld, "Self-testing/correcting with applications to numerical
  problems", *J. Comput. Syst. Sci.* 47 (1993), 549–595.
- Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Theorem 1.30.
