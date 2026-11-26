# XOR games and Tsirelson's vector characterization

In an *XOR game* the answers are bits and the predicate depends only on $a \oplus b$: the referee accepts iff $a \oplus b = f(x, y)$ for a function $f : X \times Y \to \{0,1\}$. The bias of a strategy is $\sum_{x,y} \mu(x,y) (-1)^{f(x,y)} \mathbb{E}[(-1)^{a \oplus b}]$. Tsirelson's theorem: a matrix $(c_{xy})$ is the correlation matrix $c_{xy} = \langle \psi, (A_x \otimes B_y) \psi\rangle$ of $\pm1$ observables on some entangled state iff there are real unit vectors $u_x, v_y$ in some Euclidean space with $c_{xy} = \langle u_x, v_y\rangle$. Hence the entangled bias of an XOR game equals the value of a semidefinite program, $\max_{\|u_x\| = \|v_y\| = 1} \sum_{x,y} \mu(x,y) (-1)^{f(x,y)} \langle u_x, v_y \rangle$; for CHSH it is $1/\sqrt 2$.

## Proof sketch

Given observables, the vectors $u_x = (A_x \otimes 1)\psi$ and $v_y = (1 \otimes B_y)\psi$ are unit vectors with the right inner products (in the real span of the complex vectors). Conversely, unit vectors in $\mathbb{R}^d$ are realized by observables $\sum_i u_{x,i}\Gamma_i$ built from anticommuting Clifford generators on a maximally entangled state.

## Depends on

- [Entangled strategies and the entangled value of a game](entangled-strategies-and-entangled-value.md)

## Proof depends on

- [Projective strategies suffice (Naimark dilation)](projective-strategies-suffice.md)

## Sources

- B. S. Cirel'son, "Quantum Generalizations of Bell's Inequality", Letters in Mathematical Physics 4(2), 1980.
- R. Cleve, P. Høyer, B. Toner and J. Watrous, "Consequences and Limits of Nonlocal Strategies", IEEE Conference on Computational Complexity, 2004.
