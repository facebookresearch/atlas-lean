# Transversal gate

Consider $m$ blocks of an $n$-qubit code, so $mn$ qubits, where qubit $i$ of block $\ell$ is the $i$-th qubit of that
block. A unitary $U$ on the $mn$ qubits is transversal if

$$U = \bigotimes_{i=1}^{n} U_i ,$$

where $U_i$ acts only on the $m$ qubits numbered $i$ in the $m$ blocks. A transversal unitary never couples two qubits of
the same block, so it maps an error on one qubit to an error on the corresponding qubits of the blocks, at most one per
block; this makes it fault tolerant. The $U_i$ need not be equal; "transversal $V$" usually means $V^{\otimes n}$.
Permuting qubits within a block is not allowed, since composing such gates could carry two errors into one block.

Eastin and Knill use the same notion for codes on arbitrary subsystems: a transversal partition groups the subsystems
into parts containing one subsystem of each block, and transversal operators couple only subsystems in the same part.

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 5.1.
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.3.
- B. Eastin and E. Knill, *Restrictions on transversal encoded quantum gate sets*, Phys. Rev. Lett. 102 (2009), 110502, arXiv:0811.4262, the definition of transversal operators.
