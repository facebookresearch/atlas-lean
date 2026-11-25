# Feasible CONSENSUS PATTERNS instances

An instance $(a, (s_1, \dots, s_k), L, D)$ is feasible for CONSENSUS PATTERNS when some median string $t$ of length $L$ over the letters $0, \dots, a-1$, together with a length-$L$ substring $t_i$ of every string $s_i$ (starting at a position $j_i$ with $j_i + L \le |s_i|$), satisfies $\sum_i d_H(t, t_i) \le D$, where $d_H$ is the Hamming distance.
