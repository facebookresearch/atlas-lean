# Run of a Moore machine

The run of a Moore machine $M$ with output function $\lambda$
from a state $q$ on an input word $a_1 \cdots a_n$ is the pair
$(q_n, \lambda(q_0) \lambda(q_1) \cdots \lambda(q_n))$, where $q_0 = q$ and, for each
$1 \le i \le n$, $q_i$ is the successor of $q_{i-1}$ on $a_i$. The output word has $n + 1$
letters and begins with the output of the starting state.
