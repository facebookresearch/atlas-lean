# Göös–Lovett–Meka–Watson–Zuckerman: rectangles are nonnegative juntas

Let $g : \{0,1\}^b \times \{0,1\}^b \to \{0,1\}$ be the inner-product gadget $g(x,y) = \langle x, y\rangle \bmod 2$ with block length $b \ge 100 \log n$, and write $G = g^n$. For a combinatorial rectangle $R$ in the domain of $G$ and $z \in \{0,1\}^n$, let $\mathrm{acc}_R(z) = |R \cap G^{-1}(z)| / |G^{-1}(z)|$, the probability that a uniformly random $(x,y) \in G^{-1}(z)$ lies in $R$. Then for every $d \ge 0$ and every rectangle $R$ there is a conical junta $h$ of degree at most $d$ such that, for all $z \in \{0,1\}^n$,

$$
\mathrm{acc}_R(z) \in \bigl(1 \pm 2^{-\Theta(b)}\bigr)\, h(z) \pm 2^{-\Theta(db)}.
$$

Applied rectangle by rectangle to protocols, this gives the simulation theorem $\mathrm{WAPP}^{cc}(f \circ g^n) = \Theta\bigl(\mathrm{WAPP}^{dt}(f) \cdot b\bigr)$ for every partial $f : \{0,1\}^n \to \{0,1,*\}$, where a WAPP computation accepts $1$-inputs with probability in $[(1-\varepsilon)\alpha, \alpha]$ and $0$-inputs with probability in $[0, \varepsilon\alpha]$ for some $\alpha > 0$ and a constant $\varepsilon < 1/2$, and its communication cost is the communication plus $\log(1/\alpha)$, while its query cost is the number of queries.

## Proof sketch

Decompose $R$ into a disjoint union of subrectangles in which the conditional distribution of $x$ is blockwise dense on all but a set $I$ of fixed coordinates with $|I| \le d$. On each such piece the distribution of $g^n(x, y)$ restricted to the coordinates outside $I$ is close to uniform by a uniform-marginals argument, so the piece contributes approximately a conjunction on the fixed coordinates $I$.

## Depends on

- [Conical juntas and their degree](conical-junta.md)
- [Composed functions, gadgets and lifting theorems](composed-function-lifting.md)

## Sources

- M. Göös, S. Lovett, R. Meka, T. Watson, D. Zuckerman, "Rectangles are nonnegative juntas", STOC (2015); SIAM Journal on Computing 45 (2016) 1835-1869.
