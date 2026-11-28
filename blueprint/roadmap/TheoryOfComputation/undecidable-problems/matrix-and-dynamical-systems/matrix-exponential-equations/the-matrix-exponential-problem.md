# The matrix-exponential problem

The matrix-exponential problem is the decision problem whose instances are square matrices $A_1,\dots,A_k,C$ with real algebraic entries and whose question is the solvability of $\exp(A_1t_1)\cdots\exp(A_kt_k)=C$ in nonnegative reals $t_1,\dots,t_k$.

An instance of the *matrix-exponential problem* (MEP) consists of square matrices $A_1,\dots,A_k$ and $C$, all of the same dimension $n$, whose entries are real algebraic numbers (each given by its minimal polynomial and an isolating interval). The question is whether some real numbers $t_1,\dots,t_k\ge 0$ satisfy

$$
\prod_{i=1}^{k}\exp(A_it_i)=\exp(A_1t_1)\exp(A_2t_2)\cdots\exp(A_kt_k)=C,
$$

where $\exp(M)=\sum_{j\ge0}M^j/j!$. The number $k$ of matrices and the dimension $n$ are part of the input. The *commutative case* is the restriction to instances in which the $A_i$ pairwise commute.

The MEP is a continuous analogue of solving multiplicative matrix equations $A_1^{m_1}\cdots A_k^{m_k}=C$ in nonnegative integers, and it models reachability in linear hybrid automata whose modes follow linear differential equations $\dot x=A_ix$ for durations $t_i$.

## Depends on

None.

## Proof depends on

None.

## Remarks

In the commutative case the problem is decidable, even in a generalized form with complex algebraic entries and with linear constraints on the real and imaginary parts of the $t_i$; the proof reduces it to a linear-exponential problem and then to integer programming with linear forms in logarithms, using theorems of Baker, Kronecker, Lindemann and Masser.

## Sources

- Joël Ouaknine, Amaury Pouly, João Sousa-Pinto and James Worrell, "Solvability of Matrix-Exponential Equations", in *Proceedings of the 31st Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2016)*, ACM, 2016, pp. 798–806, doi:[10.1145/2933575.2934538](https://doi.org/10.1145/2933575.2934538); numbering of arXiv:1601.05002v2 ([arXiv](https://arxiv.org/abs/1601.05002v2)): Section 1.2 (decision problems), the definition of the matrix-exponential problem and of its generalized version, and Theorems 12–14 of Section 4 (the generalized problem with commuting matrices reduces to a linear-exponential problem, which reduces to an algebraic linear integer programming problem that is decidable).
