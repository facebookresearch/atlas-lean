# Arithmetization of quantified Boolean formulas

Over a nontrivial commutative ring (one with $1 \ne 0$), a quantified Boolean formula is arithmetized by reading $\mathrm{true}$ as $1$, $\mathrm{false}$ as $0$, $\neg a$ as $1 - a$, $a \wedge b$ as $ab$, $a \vee b$ as $1 - (1-a)(1-b)$, $\forall x\, \psi$ as $\psi|_{x=0} \cdot \psi|_{x=1}$ and $\exists x\, \psi$ as $1 - (1 - \psi|_{x=0})(1 - \psi|_{x=1})$. Shen's *linearization operator* $L_x$ maps a polynomial $p$ to $(1 - x)\,p|_{x=0} + x\,p|_{x=1}$, which agrees with $p$ on $\{0,1\}$ values of $x$ and has degree at most $1$ in $x$. On Boolean inputs the arithmetization takes the value $1$ exactly on true formulas.

## Depends on

- [Quantifier blocks and prenex $\Sigma_k$ quantified Boolean formulas](quantifier-blocks-of-qbf.md)

## Sources

- C. Lund, L. Fortnow, H. Karloff and N. Nisan, "Algebraic Methods for Interactive Proof Systems", Journal of the ACM 39(4), 859–868, 1992.
- A. Shamir, "IP = PSPACE", Journal of the ACM 39(4), 869–877, 1992.
- A. Shen, "IP = PSPACE: Simplified Proof", Journal of the ACM 39(4), 878–880, 1992.
