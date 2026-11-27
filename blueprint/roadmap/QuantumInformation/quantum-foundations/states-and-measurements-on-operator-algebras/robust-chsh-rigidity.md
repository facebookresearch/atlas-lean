# Robust rigidity of near-optimal CHSH observables

Let $A_0,A_1$ be self-adjoint and $B_0,B_1$ arbitrary elements of a star-ordered algebra, $\varphi$ a state, $c = 1/\sqrt2$, and suppose $\operatorname{Re}\varphi(A_0B_0+A_0B_1+A_1B_0-A_1B_1)\ge2\sqrt2-\eta$. Then

$$
\|A_0-c(B_0+B_1)\|_\varphi^2+\|A_1-c(B_0-B_1)\|_\varphi^2+\Big(4-\sum_{x}\|A_x\|_\varphi^2-\sum_y\|B_y\|_\varphi^2\Big)\le\sqrt2\,\eta .
$$

If moreover all four are self-adjoint contractions, then with $\delta = \sqrt{\sqrt2\,\eta}$: $A_0\approx_\delta c(B_0+B_1)$, $A_1\approx_\delta c(B_0-B_1)$, and $\|1-B_y^2\|_\varphi\le\delta$ for $y = 0,1$.

## Proof sketch

Expanding the two squared distances, the cross terms are $-\sqrt2$ times the real CHSH value, and $c^2(\|B_0+B_1\|^2+\|B_0-B_1\|^2) = \|B_0\|^2+\|B_1\|^2$ by the parallelogram law; rearranging gives the identity behind the inequality. For contractions every term on the left is nonnegative, so each is at most $\sqrt2\eta$, and $\|1-B^2\|_\varphi^2\le1-\|B\|_\varphi^2$ for a self-adjoint contraction.

## Depends on

- [States on star-ordered algebras, state-dependent norm and approximation](algebraic-states-and-state-dependent-norm.md)

## Proof depends on

- [Tsirelson's inequality for self-adjoint contractions in any state](tsirelson-inequality-for-states.md)

## Sources

- S. J. Summers and R. Werner, "Maximal violation of Bell's inequalities is generic in quantum field theory", Communications in Mathematical Physics 110:247-259, 1987.
- M. McKague, T. H. Yang and V. Scarani, "Robust self-testing of the singlet", Journal of Physics A: Mathematical and Theoretical 45:455304, 2012.
