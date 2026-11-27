# Truth-table reductions to R_{K^t} for every machine and time bound lie in PSPACE

Languages truth-table reducible in polynomial time to the time-bounded random strings for every efficient universal prefix machine and every large time bound lie in PSPACE with a super-constant amount of advice; with a more permissive notion of efficient universal machine the advice disappears and the class sits between BPP and $\mathrm{PSPACE}\cap\mathrm{P}/\mathrm{poly}$.

1. For every computable unbounded $\alpha(n)=\omega(1)$,

$$
\mathrm{DTTR}_t\subseteq\mathrm{PSPACE}/\alpha(n).
$$

2. For a function $f$, a prefix machine $U$ is an *$f$-efficient universal prefix machine* if there are constants $c_M$ for each prefix machine $M$ with $K_U(x)\le K_M(x)+c_M$ and $K^t_U(x)\le K^{t'}_M(x)+c_M$ for all $x$ whenever $t(n)>f(t'(n))$. Let $\mathrm{DTTR}'_t$ be the class of languages $L$ such that for every computable $f$ there is $t_0$ with $L\le^p_{tt}R_{K^t_U}$ for all $f$-efficient universal prefix machines $U$ and all $t\ge t_0$. Then

$$
\mathrm{BPP}\subseteq\mathrm{DTTR}'_t\subseteq\mathrm{PSPACE}\cap\mathrm{P}/\mathrm{poly}.
$$

For time-unbounded prefix complexity, the class of decidable sets polynomial-time truth-table reducible to $R_{K_U}$ for every universal prefix machine $U$ was earlier shown to satisfy $\mathrm{BPP}\subseteq\mathrm{DTTR}\subseteq\mathrm{PSPACE}$, and it is open whether it lies in P/poly.

## Expansion

The proof adapts the time-unbounded PSPACE upper bound. For a language outside $\mathrm{PSPACE}/\alpha(n)$ it constructs a time-efficient universal prefix machine, via a time-bounded analogue of the coding theorem built from the Kraft inequality $\sum_x 2^{-K^t_U(x)}\le 1$, that assigns short descriptions to queries so that the given truth-table reduction errs. Allowing $f$-efficient machines with very fast-growing $f$ removes the advice; the P/poly bound comes from the small-circuit theorem for reductions to $R_{K^t}$.

## Depends on

- [Sets of Kolmogorov-random strings R_C, R_K and R_{K^t}](kolmogorov-random-strings.md)
- [Reductions to time-bounded random strings for fast-growing time bounds give P/poly](reductions-to-time-bounded-random-strings-in-ppoly.md)

## Proof depends on

None.

## Sources

- Eric Allender, Harry Buhrman, Luke Friedman and Bruno Loff, "Reductions to the set of random strings: The resource-bounded case", *Logical Methods in Computer Science* 10(3:5), 2014, DOI 10.2168/LMCS-10(3:5)2014, [arXiv:1406.7658v2](https://arxiv.org/abs/1406.7658v2) (Section 1, Theorem 4.1, Propositions 4.2 and 4.3, Definitions 5.1 and 5.2, Theorem 5.3).
