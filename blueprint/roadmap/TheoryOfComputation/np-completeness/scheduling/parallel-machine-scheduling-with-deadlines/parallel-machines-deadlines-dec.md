# The PARALLEL MACHINES WITH DEADLINES decision problem

This decision problem accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to jobs
$(p_1, d_1), \dots, (p_k, d_k)$ of natural numbers (processing times and deadlines) and a number
$m$ of machines for which there are start times $s_1, \dots, s_k \in \mathbb{N}$ and machines
$\mu_1, \dots, \mu_k \in \{0, \dots, m - 1\}$ such that $s_j + p_j \le d_j$ for every $j$, and
for all $a \ne b$ with $\mu_a = \mu_b$, either $s_a + p_a \le s_b$ or $s_b + p_b \le s_a$. It
rejects every bitstring that does not decode.
