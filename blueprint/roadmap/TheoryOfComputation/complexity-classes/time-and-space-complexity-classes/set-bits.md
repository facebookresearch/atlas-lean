# Setting two bits of an index

For natural numbers $N$, $s$, $i$, $j$ and a pair
$b = (b_1, b_2)$ of bits, this is the index in $\{0, \dots, 2^N - 1\}$ given by
$(s - s_i 2^i - s_j 2^j + b_1 2^i + b_2 2^j) \bmod 2^N$, where $s_k$ is bit $k$ of $s$ and
each subtraction of natural numbers is truncated at $0$. When $i \ne j$ this is $s$ with
bit $i$ set to $b_1$ and bit $j$ set to $b_2$, reduced modulo $2^N$.

## Sources

- A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum Computation, American Mathematical Society, 2002, Section 14.4.
