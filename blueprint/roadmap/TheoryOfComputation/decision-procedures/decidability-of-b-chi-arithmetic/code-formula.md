# Gödel numbers of Büchi formulas

Let $n \in \mathbb{N}$. The Gödel number of a formula of Büchi arithmetic with no free variables and $n$ bound variables in scope is defined by recursion on the formula, built from $\bot$, equality, the relation $V_2$, implication and universal quantification:

$$\begin{aligned} \ulcorner \bot \urcorner &= 0, & \ulcorner t_1 = t_2 \urcorner &= \pi\big(1, \pi(\ulcorner t_1 \urcorner, \ulcorner t_2 \urcorner)\big), \\ \ulcorner R(t_1, \dots, t_l) \urcorner &= \pi\big(2, \pi(\ulcorner R \urcorner, \langle \ulcorner t_1 \urcorner, \dots, \ulcorner t_l \urcorner \rangle)\big), & \ulcorner \varphi \to \psi \urcorner &= \pi\big(3, \pi(\ulcorner \varphi \urcorner, \ulcorner \psi \urcorner)\big), \\ \ulcorner \forall \varphi \urcorner &= \pi(4, \ulcorner \varphi \urcorner), \end{aligned}$$

where $\ulcorner t \urcorner$ is the Gödel number of a term, $\ulcorner V_2 \urcorner = 0$, and $\langle \cdot \rangle$ is the tuple code built by iterated pairing. Here $\pi$ is the pairing function on $\mathbb{N}$ given by $\pi(a, b) = b^2 + a$ if $a < b$ and $\pi(a, b) = a^2 + a + b$ otherwise, a bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$. Each constructor carries its own tag $0$ to $4$.
