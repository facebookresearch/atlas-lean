# Certifying remote points for circuits of decision trees

If every output of a circuit $C:\Sigma^n\to\{\pm1\}^m$ is a $t$-query decision tree and $m$ is large enough, then a string drawn from any sufficiently almost $k$-wise independent distribution is, with high probability, $(\frac12-\varepsilon)$-far from the range of $C$, and a deterministic algorithm certifies this.

For $x,y\in\{\pm1\}^m$ let $\Delta(x,y)=\frac1m\sum_{i}\mathbf{1}\{x_i\ne y_i\}$. A distribution on $\{\pm1\}^m$ is $\eta$-almost $k$-wise independent if its projection onto any $k$ coordinates is within total variation distance $\eta$ of uniform. There is a universal constant $c_{\mathrm{remote}}>0$ such that the following holds. Let $k,t,w,n,m\ge 1$ be integers with $k\ge t\log n$, let $\varepsilon\in(0,1)$, let $|\Sigma|=2^w$, and let $\mathcal{D}$ be $\eta$-almost $k$-wise independent on $\{\pm1\}^m$ with $\eta\le(2^{-tw}\cdot\varepsilon^4\cdot n^{-k/\log n})^{O(1)}$. Let $C:\Sigma^n\to\{\pm1\}^m$ be a circuit each of whose outputs $C(x)_i$ is computed by a $t$-query adaptive decision tree over $x$. If

$$
m\ge c_{\mathrm{remote}}\cdot n\cdot\left(\frac{n\log n}{k}\right)^{t/2-1}\cdot\log n\cdot\varepsilon^{-4}\cdot 2^{O(tw)},
$$

then

$$
\Pr_{b\sim\mathcal{D}}\left[\min_{x\in\Sigma^n}\Delta(C(x),b)\ge\frac12-\varepsilon\right]\ge 1-\frac{1}{\mathrm{poly}(n)},
$$

and a deterministic algorithm running in time $\mathrm{poly}(m,n^{O(t)})$ outputs "certified" or "uncertain", outputs "certified" with probability $1-1/\mathrm{poly}(n)$ over $b\sim\mathcal{D}$, and the bound holds whenever it outputs "certified".

This covers odd $t$, which Korten, Pitassi and Impagliazzo left open, and when each output is a simple predicate of $t$ inputs and $b$ is uniform it is exactly semi-random $t$-CSP refutation.

## Expansion

The XOR principle reduces the claim $C(x)=b$ to strong refutation of $t$-XOR instances: when the inputs are bits ($w=1$) and each output $C(x)_i$ is a $t$-junta, expanding it into its at most $2^t$ Fourier characters (each a multiple of $2^{-t}$) shows that some weighted $t$-XOR instance has value at least $2^{-t}$; in the general case of $t$-query adaptive decision trees over $\Sigma=\{0,1\}^w$, Section 2.3 of the source bounds the Fourier $\ell_1$-mass of each output by $2^{tw}$ supported on at most $4^{tw}$ characters (each meeting at most one $w$-bit group per layer) and groups them into weighted $t$-XOR instances. The Hsieh–Kothari–Mohanty trace-method refutation bounds $\mathbb{E}_b[\mathrm{tr}(A_b^{\ell})]$ for $\ell\approx t\log n$, a degree-$\ell$ polynomial in $b$, so it works verbatim when $b$ is only $\ell$-wise almost independent.

## Depends on

- [The remote point problem](remote-point-problem.md)
- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](../../complexity-classes/tfnp-hierarchies-and-avoidance/range-avoidance-and-explicit-constructions/range-avoidance-problem.md)

## Proof depends on

None.

## Sources

- Venkatesan Guruswami, Xin Lyu and Weiqiang Yuan, "Cell-Probe Lower Bounds via Semi-Random CSP Refutation: Simplified and the Odd-Locality Case", *ACM-SIAM Symposium on Discrete Algorithms (SODA)*, 2026, arXiv:2507.22265v1 (Theorem 1, Lemma 2.1, Definitions 3.1 to 3.4, Theorems 7 to 9, Sections 2 to 4).
