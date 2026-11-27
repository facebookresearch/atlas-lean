# Measurements, agreement and character observables in a star-ordered algebra

A *measurement* with finite outcome set $\alpha$ in a star-ordered algebra $\mathcal{A}$ is a family of effects $E_a\ge 0$ with $\sum_a E_a = 1$; it is *projective* if each $E_a$ is idempotent (in a C*-algebra the effects of a projective measurement are then pairwise orthogonal). In a state $\varphi$ outcome $a$ has probability $\operatorname{Re}\varphi(E_a)$; on matrices with a vector state this is the Born rule for the POVM $(E_a)$. Post-processing by $f:\alpha\to\beta$ has effects $\sum_{f(a)=b}E_a$. For two measurements $P,Q$ with the same outcomes and commuting effects, their *agreement* in $\varphi$ is $\sum_a\operatorname{Re}\varphi(P_aQ_a)$, the probability that jointly performing them gives equal outcomes. For outcomes in $\{0,1\}^n$, the *character observables* are $\chi_M(a) = \sum_x(-1)^{a\cdot x}M_x$ for $a\in\{0,1\}^n$; if $M$ is projective they are self-adjoint unitaries and exactly linear, $\chi_M(a)\chi_M(a') = \chi_M(a+a')$. Pairwise commuting $\pm1$ observables $O_1,\dots,O_m$ are measured jointly by the projective measurement with effects $\prod_j(1+(-1)^{a_j}O_j)/2$, $a\in\{0,1\}^m$; if $\prod_jO_j = c\cdot 1$ then outcomes with $\prod_j(-1)^{a_j}\ne c$ have zero effect.

## Depends on

- [States on star-ordered algebras, state-dependent norm and approximation](algebraic-states-and-state-dependent-norm.md)
- [Positive-operator-valued measurements and the Born rule](../../quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)
- [Walsh character on the Boolean cube](../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-walsh-char.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "MIP* = RE", arXiv:2001.04383, 2020.
- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017.
- M. de la Salle, "Orthogonalization of positive operator valued measures", Comptes Rendus. Mathematique 360:549-560, 2022.
