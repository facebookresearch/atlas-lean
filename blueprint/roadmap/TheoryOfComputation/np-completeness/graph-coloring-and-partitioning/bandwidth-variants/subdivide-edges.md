# Edges after subdividing an edge list

Given a first fresh vertex $f$, a list of edges $(a_0, b_0), (a_1, b_1), \dots$ and a list of counts $m_0, m_1, \dots$, the subdivided edges begin with the consecutive pairs of the path $a_0, f, f+1, \dots, f + m_0 - 1, b_0$ when $m_0 > 0$, and with the edge $(a_0, b_0)$ itself when $m_0 = 0$. They continue with the remaining edges and counts from the fresh vertex $f + m_0$. The output stops when either list runs out.
