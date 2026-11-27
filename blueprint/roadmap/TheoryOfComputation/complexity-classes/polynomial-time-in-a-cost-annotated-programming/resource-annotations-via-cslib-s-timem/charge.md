# Charging a cost before a computation

A cost is a triple $(t, s, m)$ of natural numbers recording time, cumulative space and peak memory. The sum of $(t_1, s_1, m_1)$ and $(t_2, s_2, m_2)$ is $(t_1 + t_2,\ s_1 + s_2,\ \max(m_1, m_2))$, and the zero cost is $(0, 0, 0)$. A cost-annotated computation returns a value together with an accumulated cost. Charging a cost $c$ before a computation $x$ gives the computation that first records the cost $c$ and then runs $x$: it returns the value of $x$, with accumulated cost $c$ plus the cost of $x$.
