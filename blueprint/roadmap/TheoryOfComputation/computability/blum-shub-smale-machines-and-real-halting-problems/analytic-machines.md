# Analytic machines

An analytic machine is a Blum-Shub-Smale machine that, instead of halting with an exact output, prints an infinite sequence of vectors
approximating it, with error bounds (strongly analytic) or without them (weakly analytic).

An *analytic machine* is a [Blum-Shub-Smale machine](blum-shub-smale-machines-their-halting-problems.md), with exact arithmetic operations and tests,
that prints a sequence $(\vec y_n)_n$ of vectors in $\mathbb{R}^* = \bigcup_d \mathbb{R}^d$ instead of halting. Writing $\lVert \vec y \rVert = \sum_i |y_i|$ for the $1$-norm, it
computes a partial function $f :\subseteq \mathbb{R}^* \to \mathbb{R}^*$ *strongly* if on every input $\vec x \in \mathrm{dom}(f)$ it prints an infinite sequence with
$\dim \vec y_n = \dim f(\vec x)$ and $\lVert \vec y_n - f(\vec x) \rVert \le 2^{-n}$ for all $n$, and *weakly* if $\dim \vec y_n = \dim f(\vec x)$ for all but finitely many $n$
and $\vec y_n \to f(\vec x)$; on inputs outside $\mathrm{dom}(f)$ these conditions must fail. Machines that compute strongly or weakly in this sense are
*strongly* or *weakly analytic*. A machine may also stop printing after finitely many vectors.

## Depends on

- [Blum-Shub-Smale machines and their halting problems](blum-shub-smale-machines-their-halting-problems.md)

## Proof depends on

None.

## Expansion

This page states a definition.

## Sources

- T. Gärtner and M. Ziegler, "Real analytic machines and degrees", *Logical Methods in Computer Science* 7(3), paper 11, 2011, doi:10.2168/LMCS-7(3:11)2011; read in arXiv:1006.0398v3: Section 1.6 (analytic machines, Equation (1.4)) and Remark 1.4, with the convention for finite output sequences from Section 3.1.
