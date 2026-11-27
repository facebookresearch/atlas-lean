# Hirahara–Ilango–Williams: every compression problem has circuits of size 2^{4ℓ/5}·poly(t), beating brute force for MCSP and K^t

Let $\mathrm{Eval}:\{0,1\}^*\to\{0,1\}^*$ be polynomial-time computable. The **Eval compression problem** asks, given $x\in\{0,1\}^n$ and a size bound $s$, to output some $y$ with $|y|\le s$ and $\mathrm{Eval}(y)=x$, or $\bot$ if none exists; brute force takes time $O(2^{s}\cdot t(n))$ where $t(n)$ bounds the running time of $\mathrm{Eval}$ on descriptions of length $s$. There is a (non-uniform) circuit family $\{C_{n,s}\}$ of size

$$
2^{4s/5}\cdot\mathrm{poly}(n,s,t(n))
$$

such that $C_{n,s}(x)$ outputs a description of length at most $s$ for every $x\in\{0,1\}^n$ that has one. Consequences: for every fixed polynomial time bound $t$, finding a description witnessing $K^{t}(x)\le\ell$ has circuits of size $2^{4\ell/5}\cdot\mathrm{poly}(t)$; and Search-MCSP for circuits of size $s(n)$ on truth tables of length $2^n$ has circuits of size $2^{4w/5+o(w)}\cdot\mathrm{poly}(2^n)$ with $w=s(n)\log_2(s(n)+n)$, beating the $2^{O(w)}$ enumeration of all size-$s(n)$ circuits for every $s(n)\ge n$.

## Proof sketch

The construction adapts the Fiat–Naor data structure for function inversion: view $\mathrm{Eval}$ restricted to length-$s$ inputs as a function to be inverted, store chains of iterated (re-randomized) evaluations as advice, and answer an inversion query by walking chains; the trade-off between advice and walking time yields the exponent $4/5$. Implementing the queries by Boolean circuits requires hashing the outputs down so that the circuit size depends exponentially only on the description length $s$ and polynomially on $n$ and $t(n)$.

## Depends on

- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)

## Proof depends on

- [Pairwise-independent hashing by affine maps over GF(2)](../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- Shuichi Hirahara, Rahul Ilango and R. Ryan Williams, "Beating Brute Force for Compression Problems", STOC (2024), ECCC TR23-171.
