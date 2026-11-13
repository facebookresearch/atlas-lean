# Initial state of a BQP computation

For a bitstring $x = (x_0, \dots, x_{n-1})$, with
true read as $1$ and false as $0$, and a number $a$ of ancilla qubits, the initial state is the
tensor product of the computational basis state of $x$ and the all-zero state on $a$ qubits: the
vector on $\{0, \dots, 2^{n+a} - 1\}$ whose value at $s$ is the value of the basis state of $x$ at
$s \bmod 2^n$ times the value of the all-zero state at $\lfloor s / 2^n \rfloor$. So $x$ occupies
the $n$ low-order bits of the index, and the state equals $1$ at the index $\sum_{k < n} x_k 2^k$
and $0$ elsewhere.

## Sources

- M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press, 2000, Chapter 4 (quantum circuits); S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Definition 10.1.
