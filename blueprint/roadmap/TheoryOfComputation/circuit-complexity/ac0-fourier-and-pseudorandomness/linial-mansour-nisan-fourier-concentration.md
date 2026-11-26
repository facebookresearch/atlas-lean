# Linial–Mansour–Nisan: AC0 functions have concentrated Fourier spectra

There is a constant $c$ such that for every circuit over the unbounded fan-in basis of depth $d$ with $g$ gates computing $f:\{0,1\}^n\to\{0,1\}$ and every $k$,

$$
\sum_{|S|\ge k}\widehat{F}(S)^2\le 2g\cdot 2^{-c\,k^{1/d}},\qquad F=(-1)^f .
$$

In an explicit form: for $s\ge2$, the Fourier weight on sets of size at least $k$ is at most $2g/2^s$ whenever $\max(8,2s,n)\le k\lfloor n/(16s+1)^d\rfloor$, which gives $g\,2^{-\Omega(k^{1/(d+1)})}$ when depth counts negations.

## Proof sketch

Apply a random restriction leaving a random set of $\ell=\lfloor n/(16s+1)^d\rfloor$ variables free; by Håstad's switching lemma the restricted circuit is a decision tree of depth below $s$ except with probability $g2^{-s}$, so its Fourier spectrum has degree below $s$. A random restriction maps high-degree Fourier weight of $f$ to weight of degree at least $s$ with constant probability, which bounds the tail.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Unbounded fan-in signature](../unbounded-fan-in-circuits/ac-signature.md)

## Proof depends on

- [Håstad's switching lemma](../lower-bounds-for-ac0-circuits/hastad-s-switching-lemma.md)

## Sources

- Nathan Linial, Yishay Mansour, Noam Nisan, "Constant Depth Circuits, Fourier Transform, and Learnability", Journal of the ACM, 1993.
- Ryan O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
