# Tsirelson's inequality for self-adjoint contractions in any state

Let $A_0,A_1,B_0,B_1$ be self-adjoint elements of a star-ordered algebra with $A_x^2\le1$ and $B_y^2\le1$, and let $\varphi$ be any state. Then

$$
\operatorname{Re}\varphi\big(A_0B_0+A_0B_1+A_1B_0-A_1B_1\big)\le2\sqrt2 .
$$

No commutation between the $A_x$ and $B_y$ and no involution property is assumed, so the bound covers the observables $E_0-E_1$ of arbitrary two-outcome measurements in any model (tensor-product or commuting-operator).

## Proof sketch

In the GNS pre-inner-product space of $\varphi$ the elements become vectors $a_x, b_y$ of norm at most one with $\varphi(A_xB_y) = \langle a_x,b_y\rangle$. Then the CHSH expression is $\operatorname{Re}\langle a_0,b_0+b_1\rangle+\operatorname{Re}\langle a_1,b_0-b_1\rangle\le\|b_0+b_1\|+\|b_0-b_1\|\le\sqrt{2(\|b_0+b_1\|^2+\|b_0-b_1\|^2)}\le2\sqrt2$ by the parallelogram law.

## Depends on

- [States on star-ordered algebras, state-dependent norm and approximation](algebraic-states-and-state-dependent-norm.md)

## Proof depends on

- [Existence of a unit cyclic vector in the GNS space](../../../Analysis/operator-algebras/gns-construction/exists-gns-cyclic-vector.md)

## Sources

- B. S. Cirel'son, "Quantum generalizations of Bell's inequality", Letters in Mathematical Physics 4:93-100, 1980.
