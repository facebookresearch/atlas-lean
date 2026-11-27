# Boundedness of all products of two matrices is undecidable

No algorithm decides whether the set of all products of matrices from a finite set of rational matrices is bounded, or whether its joint spectral radius is at most $1$; both problems stay undecidable for sets of two matrices.

For a finite set $\Sigma$ of $n \times n$ matrices and an induced matrix norm $\|\cdot\|$, let

$$
\hat\rho_k(\Sigma) = \max \{ \|A_1 A_2 \cdots A_k\|^{1/k} : A_1, \dots, A_k \in \Sigma \}
$$

for $k \ge 1$. The *joint spectral radius* $\rho(\Sigma) = \lim_{k \to \infty} \hat\rho_k(\Sigma)$ of Rota and Strang exists and does not depend on the induced norm. It governs the growth of the switched system $x_{t+1} = A_t x_t$ with each $A_t \in \Sigma$ chosen arbitrarily.

**Theorem (Blondel and Tsitsiklis).** For finite sets $\Sigma$ of matrices with rational entries, it is undecidable whether the set of all products $A_1 \cdots A_k$ of matrices of $\Sigma$ is bounded, and it is undecidable whether $\rho(\Sigma) \le 1$. Both problems remain undecidable when $\Sigma$ consists of only two matrices.

In contrast, $\rho(\Sigma)$ can be approximated to any accuracy, which yields procedures that recognize $\rho(\Sigma) > 1$ and $\rho(\Sigma) < 1$ but need not terminate when $\rho(\Sigma) = 1$. Whether $\rho(\Sigma) < 1$ is decidable was open when the survey was written.

## Depends on

None.

## Proof depends on

None.

## Expansion

The survey states the result without proof. It notes the related fact that the mortality problem reduces to computing the joint spectral radius: for integer matrices either $\rho(\Sigma) = 0$, exactly when $\Sigma$ is mortal, or $\rho(\Sigma) \ge 1$. A good expansion would give the reduction of the original paper and link the undecidable problem it starts from; neither has a page yet.

## Sources

- V. D. Blondel and J. N. Tsitsiklis, "A survey of computational complexity results in systems and control", *Automatica* 36(9) (2000), pp. 1249–1274, doi:10.1016/S0005-1098(00)00050-9; read in the author copy at <http://web.mit.edu/people/jnt/Papers/J080-00-vb-survey.pdf>: Section 3.5 (time-varying systems: the joint spectral radius, the list of questions, the undecidability of boundedness and of $\rho(\Sigma) \le 1$ even for two matrices, the approximation procedures and the open status of $\rho(\Sigma) < 1$), and the opening discussion of models of computation (inputs taken to be integer or rational).
- V. D. Blondel and J. N. Tsitsiklis, "The boundedness of all products of a pair of matrices is undecidable", *Systems & Control Letters* 41(2) (2000), doi:10.1016/S0167-6911(00)00049-9 (cited, not read).
