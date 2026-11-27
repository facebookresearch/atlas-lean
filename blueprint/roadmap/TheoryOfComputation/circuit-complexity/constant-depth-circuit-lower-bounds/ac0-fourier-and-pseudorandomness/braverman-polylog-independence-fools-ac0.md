# Braverman: polylogarithmic independence fools AC0

For every $d$ there is a polynomial $p_d$ such that every $k$-wise independent distribution on $\{0,1\}^n$ $\varepsilon$-fools every circuit of depth $d$ and size $m$ over NOT and unbounded fan-in AND and OR gates (the unbounded fan-in basis without MOD gates), provided $k\ge p_d(\log(m/\varepsilon))$. Explicitly (Braverman's main theorem): for every $s\ge\log m$, if $\mu$ is $r$-wise independent with

$$
r\ge 3\cdot 60^{d+3}\cdot(\log m)^{(d+1)(d+3)}\cdot s^{d(d+3)},
$$

then $|\mathbb{E}_\mu[F]-\mathbb{E}[F]|<0.82^{s}\cdot 15m$ for every Boolean function $F$ computed by such a circuit; taking $s=5\log(15m/\varepsilon)$ gives $k=(\log(m/\varepsilon))^{O(d^2)}$. Tal improved the requirement to $k=O(\log(m/\varepsilon))^{3d+3}$.

## Proof sketch

Take Braverman's real approximator $f$ of degree $(s\log m)^d$, which agrees with $F$ outside an error set whose indicator $E$ is itself computed by a small circuit of depth below $d+3$ and has small mass under both the uniform distribution and $\mu$. Replace $E$ by its low-degree LMN approximation $\tilde E$ and set $f'=f\cdot(1-\tilde E)$; this gives a one-sided low-degree approximator of $F$ that is close to $F$ in $\ell_2$ and agrees with it on most of the mass of both distributions. Low-degree polynomials have equal expectations under $\mu$ and uniform, which bounds the fooling error.

## Depends on

- [k-wise independent and almost k-wise independent distributions](k-wise-independent-distributions.md)
- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)

## Proof depends on

- [Braverman's real gate approximators](braverman-real-gate-approximators.md)
- [Linial–Mansour–Nisan: AC0 functions have concentrated Fourier spectra](linial-mansour-nisan-fourier-concentration.md)

## Sources

- Mark Braverman, "Polylogarithmic Independence Fools AC^0 Circuits", Journal of the ACM 57(5), Article 28, 2010 (Main Theorem and Corollary 2; Lemmas 7, 8, 10, 11 for the proof).
- Avishay Tal, "Tight Bounds on the Fourier Spectrum of AC^0", 32nd Computational Complexity Conference (CCC 2017), LIPIcs 79, 2017 (improved bound $O(\log(m/\varepsilon))^{3d+3}$).
