# Exactly linear observables from the quantum linearity and consistency tests

Let $\varphi$ be a state on $M_{\iota\times\kappa}(\mathbb{C})$. Let $A(c)$, $c\in\{0,1\}^n$, be $\pm1$ observables on $\mathbb{C}^\iota$ and $N_1(a,b),N_2(a,b)$ matrices on $\mathbb{C}^\kappa$ with $N_1(a,b)$ unitary. Suppose

$$
\mathbb{E}_{a,b}\operatorname{Re}\varphi\big((I\otimes N_1(a,b))(I\otimes N_2(a,b))(A(a+b)\otimes I)\big)\ge1-\varepsilon,
$$

$\mathbb{E}_{a,b}\|A(a)\otimes I-I\otimes N_1(a,b)\|_\varphi^2\le\eta_1$ and $\mathbb{E}_{a,b}\|A(b)\otimes I-I\otimes N_2(a,b)\|_\varphi^2\le\eta_2$. Then there is a projective measurement $P$ on $\mathbb{C}^\iota$ with unitary, exactly linear character observables and

$$
\mathbb{E}_a\|(A(a)-\chi_P(a))\otimes I\|_\varphi^2\le40\big(\varepsilon+\sqrt{\eta_1}+\sqrt{\eta_2}\big).
$$

## Proof sketch

First derive linearity from consistency: moving each factor $A(a)$, $A(b)$ to the other player's consistent copy and commuting it past the first player's operators gives $\mathbb{E}_{a,b}\operatorname{Re}\varphi(A(a)A(b)A(a+b)\otimes I)\ge1-\varepsilon-\sqrt{\eta_1}-\sqrt{\eta_2}$, each swap costing a state distance by Cauchy-Schwarz. Then apply same-space rounding to the first player's observables in the pulled-back state.

## Depends on

- [States on star-ordered algebras, state-dependent norm and approximation](../states-and-measurements-on-operator-algebras/algebraic-states-and-state-dependent-norm.md)
- [Measurements, agreement and character observables in a star-ordered algebra](../states-and-measurements-on-operator-algebras/algebraic-measurements-and-agreement.md)

## Proof depends on

- [Rounding approximately linear observables to exactly linear ones on the same space](rounding-approximately-linear-observables.md)

## Sources

- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017.
