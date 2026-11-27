# Linial–Mansour–Nisan: AC0 functions have concentrated Fourier spectra

Let $f:\{0,1\}^n\to\{0,1\}$ be computed by a circuit over the unbounded fan-in basis of depth $d$ and size $M$, and let $F=(-1)^f$. Then for every integer $t$,

$$
\sum_{|S|>t}\widehat{F}(S)^2\le 2M\cdot 2^{-t^{1/d}/20}.
$$

Equivalently, $F$ is approximated in $\ell_2$ by its Fourier truncation to degree $t$ with squared error at most $2M\,2^{-t^{1/d}/20}$. Tal later sharpened the tail to $2\cdot 2^{-\Omega(t/(\log M)^{d-1})}$.

## Proof sketch

Let $\rho$ be a random restriction leaving each variable free with probability $p=1/(10\,t^{(d-1)/d})$ and put $s=pt/2=t^{1/d}/20$. Repeated use of Håstad's switching lemma shows that $f|_\rho$ has Fourier degree above $s$ with probability at most $M2^{-s}$. When $pt\ge8$, a Chernoff bound shows that a set $A$ with $|A|>t$ keeps more than $pt/2$ free variables with probability at least $1/2$, so $\sum_{|S|>t}\widehat F(S)^2\le 2\,\mathbb{E}_\rho\bigl[\sum_{|S|>s}\widehat{F|_\rho}(S)^2\bigr]\le 2M2^{-s}$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)

## Proof depends on

- [Håstad's switching lemma](../../lower-bounds-for-ac0-circuits/hastad-s-switching-lemma.md)

## Sources

- Nathan Linial, Yishay Mansour, Noam Nisan, "Constant Depth Circuits, Fourier Transform, and Learnability", Journal of the ACM 40(3), 1993 (Main Lemma, Lemma 7; Lemmas 2 and 6 for the proof).
- Avishay Tal, "Tight Bounds on the Fourier Spectrum of AC^0", 32nd Computational Complexity Conference (CCC 2017), LIPIcs 79, 2017.
- Ryan O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
