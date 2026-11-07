# The 2-local Hamiltonian problem is QMA-complete

The 2-local Hamiltonian promise
problem, given by its yes-instances and no-instances, is in QMA, and every promise problem in QMA
whose sets of yes-instances and no-instances are disjoint sets of bitstrings has a polynomial-time
reduction to it.

Here an instance encodes a number $n$ of qubits, a list of $m$ valid 2-local terms on $n$ qubits
and encoded rationals $a$ and $b$ with $b - a \ge 1/(m + 1)$; it is a yes-instance when the
Hamiltonian of the terms on $n$ qubits is Hermitian with ground energy at most $a$, and a
no-instance when it is Hermitian with ground energy at least $b$.

## Sources

- A. Y. Kitaev, "Quantum NP", talk at AQIP 1999; A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum Computation, American Mathematical Society, 2002, Section 14.4; J. Kempe, A. Y. Kitaev, and O. Regev, "The complexity of the local Hamiltonian problem", SIAM Journal on Computing 35 (2006), 1070-1097 (the 2-local reduction); A. D. Bookatz, "QMA-complete problems", arXiv:1212.6312 (2012), Section 2 (survey of the QMA-completeness of the local Hamiltonian problem); S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Chapter 10, for the QMA-completeness of 2-local Hamiltonian.
