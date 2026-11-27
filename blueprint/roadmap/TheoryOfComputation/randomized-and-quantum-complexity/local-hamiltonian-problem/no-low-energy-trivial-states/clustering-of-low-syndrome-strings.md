# Clustering of low-syndrome strings for codes with small-set boundary expansion

Let $(H_X, H_Z)$ define a CSS code such that $H_Z$ has *small-set boundary expansion*: there are constants $\gamma, c > 0$ with $|H_Z x| \ge c\, |x|_{\mathrm{red}}$ whenever $|x|_{\mathrm{red}} \le \gamma n$, where $|x|_{\mathrm{red}} = \min_{y \in \mathrm{im} H_X^{T}} |x + y|$. Then for every $\eta$ with $0 \le \eta < c\gamma$, every $x$ with $|H_Z x| \le \eta n$ satisfies either $|x|_{\mathrm{red}} \le (\eta/c) n$ or $|x|_{\mathrm{red}} > \gamma n$. Consequently, for $0 \le \eta \le c\gamma/4$ the relation $x \sim y \iff |x + y|_{\mathrm{red}} \le (2\eta/c) n$ is an equivalence relation on $G_\eta = \{x : |H_Z x| \le \eta n\}$, and strings in distinct classes are at Hamming distance more than $\gamma n$.

## Proof sketch

If $|x|_{\mathrm{red}} \le \gamma n$, expansion gives $|x|_{\mathrm{red}} \le |H_Z x|/c \le (\eta/c) n$. For $x, y \in G_\eta$, every check violated by $x + y$ is violated by $x$ or by $y$, so $|H_Z(x+y)| \le 2\eta n$ and the dichotomy at $2\eta < c\gamma$ applies to $x + y$. If $x \sim y$ and $y \sim z$, then $|x + z|_{\mathrm{red}} \le (4\eta/c) n \le \gamma n$, so the dichotomy forces $|x + z|_{\mathrm{red}} \le (2\eta/c) n$. Strings in distinct classes satisfy $|x + y| \ge |x + y|_{\mathrm{red}} > \gamma n$.

## Depends on

- [CSS code Hamiltonians of quantum LDPC codes](css-code-hamiltonians.md)

## Sources

- Anurag Anshu, Nikolas P. Breuckmann, Chinmay Nirkhe, "NLTS Hamiltonians from good quantum codes", STOC (2023); arXiv:2206.13228.
- Anthony Leverrier, Gilles Zemor, "Quantum Tanner codes", FOCS (2022); arXiv:2202.13641.
