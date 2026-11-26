# Braverman: polylogarithmic independence fools AC0

For every $d$ there is a polynomial $p_d$ such that every $k$-wise independent distribution on $\{0,1\}^n$ $\varepsilon$-fools every circuit over the unbounded fan-in basis of depth $d$ and size $s$, provided $k\ge p_d(\log(s/\varepsilon))$. In an explicit form: if the circuit has at most $2^q$ gates, each of fan-in below $2^q$ ($q\ge1$), the error is at most $2^{-q}$ once $k\ge(64q)^{(2d+3)(d+7)+1}$.

## Proof sketch

Construct real polynomials $f_\ell\le f\le f_u$-style sandwiching approximators: combine Braverman's approximator (agreeing with the circuit on most of the mass of both the uniform distribution and $\nu$) with a low-degree LMN approximation of the error indicator; low-degree polynomials have equal expectations under $\nu$ and uniform, which bounds the fooling error.

## Depends on

- [k-wise independent and almost k-wise independent distributions](k-wise-independent-distributions.md)
- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)

## Proof depends on

- [Braverman's real gate approximators](braverman-real-gate-approximators.md)
- [Linial–Mansour–Nisan: AC0 functions have concentrated Fourier spectra](linial-mansour-nisan-fourier-concentration.md)

## Sources

- Mark Braverman, "Polylogarithmic Independence Fools AC^0 Circuits", Journal of the ACM, 2010.
- Avishay Tal, "Tight Bounds on the Fourier Spectrum of AC^0", 32nd Computational Complexity Conference (CCC 2017), 2017.
