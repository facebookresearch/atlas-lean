# Sequential projective measurements and their commutator defects

Given projective measurements $M^1,\dots,M^k$ with outcome set $\alpha$ in a star-ordered algebra, the *sequential measurement* records all outcomes: the effect of a transcript $g\in\alpha^k$ is $E_g = T_gT_g^*$ with $T_g = M^1_{g_1}M^2_{g_2}\cdots M^k_{g_k}$; these effects sum to $1$, no commutation is required, and the marginal of coordinate $i$ is $M^i_b$ sandwiched by the products of earlier outcomes. For a state $\varphi$, the *pair commutator defect* of measurements $E,M$ is $\sum_{a,b}\|E_aM_b-M_bE_a\|_\varphi^2$, the *copy defect* of $M$ against a measurement $R$ (typically the other player's commuting copy) is $\sum_b\|M_b-R_b\|_\varphi^2$, and the *prefix commutator defect* at coordinate $i$ is $\sum_{a}\sum_{p}\|M^i_aT_p^*-T_p^*M^i_a\|_\varphi^2$ over transcripts $p$ of the coordinates before $i$.

## Depends on

- [Measurements, agreement and character observables in a star-ordered algebra](../../../QuantumInformation/quantum-foundations/states-and-measurements-on-operator-algebras/algebraic-measurements-and-agreement.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum soundness of the classical low individual degree test", arXiv:2009.12982, 2020.
