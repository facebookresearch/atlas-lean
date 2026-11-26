# Addition of costs is commutative

A cost is a triple $(t, s, m)$ of natural numbers recording time, cumulative space and peak memory. The sum of $(t_1, s_1, m_1)$ and $(t_2, s_2, m_2)$ is $(t_1 + t_2,\ s_1 + s_2,\ \max(m_1, m_2))$, and the zero cost is $(0, 0, 0)$. For all costs $a, b$, $a + b = b + a$.
