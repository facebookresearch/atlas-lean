# Near-optimal CHSH observables nearly anticommute

Let $A_0,A_1,B_0,B_1$ be self-adjoint contractions in a star-ordered algebra with each $A_x$ commuting with each $B_y$, let $\varphi$ be a state, and suppose $\operatorname{Re}\varphi(A_0B_0+A_0B_1+A_1B_0-A_1B_1)\ge2\sqrt2-\eta$. Then

$$
\|A_0A_1+A_1A_0\|_\varphi\le(4+2\sqrt2)\sqrt{\sqrt2\,\eta}.
$$

## Proof sketch

By robust rigidity, $A_0\approx c(B_0+B_1)$ and $A_1\approx c(B_0-B_1)$ with error $\delta = \sqrt{\sqrt2\eta}$, and $B_y^2\approx1$. Replace the right factors of $A_0A_1$ and $A_1A_0$ by these expressions, moving them past the $A$'s using commutation; left multiplication by $c(B_0\pm B_1)$ stretches the state norm by at most $\sqrt2$. The replaced anticommutator is $c^2\big((B_0+B_1)(B_0-B_1)+(B_0-B_1)(B_0+B_1)\big) = B_0^2-B_1^2$, which is $2\delta$-close to $0$ because $B_y^2\approx_\delta1$; collecting the errors gives the stated constant.

## Depends on

- [States on star-ordered algebras, state-dependent norm and approximation](algebraic-states-and-state-dependent-norm.md)

## Proof depends on

- [Robust rigidity of near-optimal CHSH observables](robust-chsh-rigidity.md)

## Sources

- M. McKague, T. H. Yang and V. Scarani, "Robust self-testing of the singlet", Journal of Physics A: Mathematical and Theoretical 45:455304, 2012.
- S. J. Summers and R. Werner, "Maximal violation of Bell's inequalities is generic in quantum field theory", Communications in Mathematical Physics 110:247-259, 1987.
