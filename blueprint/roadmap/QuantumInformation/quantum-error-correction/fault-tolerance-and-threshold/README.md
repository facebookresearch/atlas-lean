# Fault tolerance and the threshold theorem

Concatenating a code with itself gives distance at least the product of the distances, and in a fault-tolerant simulation each level of concatenation
maps an error rate $p$ to roughly $A p^{t+1}$. Below a threshold the failure probability then falls doubly exponentially
in the number of levels: arbitrary quantum circuits can be simulated reliably with polylogarithmic overhead under local
stochastic noise. The arithmetic of the recursion is the
[error recursion for concatenated codes](../error-recursion-for-concatenated-fault-tolerant-codes.md).

- [Concatenated quantum code](concatenated-quantum-code.md)
- [Distance of a concatenated code](distance-of-a-concatenated-code.md)
- [Locations of a quantum circuit](locations-of-a-quantum-circuit.md)
- [Local stochastic error model](local-stochastic-error-model.md)
- [The threshold theorem](threshold-theorem.md)

## Related topics

- [Error recursion for concatenated fault-tolerant codes](../error-recursion-for-concatenated-fault-tolerant-codes.md): the recursion $p_{j+1} \le c\, p_j^2$ and its solution.
- [Fault-tolerant gates](../fault-tolerant-gates/README.md): the gadgets that the threshold theorem assembles.

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 5.
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Chapter 6.
- P. Aliferis, D. Gottesman and J. Preskill, *Quantum accuracy threshold for concatenated distance-3 codes*, Quantum Inf. Comput. 6 (2006), 97–165, arXiv:quant-ph/0504218.
