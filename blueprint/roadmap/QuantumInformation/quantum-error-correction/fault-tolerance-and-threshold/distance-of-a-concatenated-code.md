# Distance of a concatenated code

The [concatenation](concatenated-quantum-code.md) of an $[[n_1, k, d_1]]$ outer code with an $[[n_2, 1, d_2]]$ inner code is
an $[[n_1 n_2, k, d]]$ code with $d \ge d_1 d_2$. The inequality can be strict: Shor's code concatenates two codes of
distance $1$ (for general Pauli errors) and has distance $3$. Concatenating the five-qubit code with itself $L$ times gives
a $[[5^L, 1, d]]$ code with $d \ge 3^L$.

Proof (Gottesman): an operator in the normalizer but not in the stabilizer times phases must act as a nontrivial logical
operator of the outer code; on each block where it acts as a nontrivial logical operator of the inner code it has weight
at least $d_2$, and there are at least $d_1$ such blocks.

## Depends on

- [Concatenated quantum code](concatenated-quantum-code.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)

## Proof depends on

- [Stabilizer codes: correctability criterion and distance](../stabilizer-codes-correctability-criterion-and-distance.md)
- [Logical Pauli operators of a stabilizer code](../stabilizer-formalism/logical-pauli-operators-of-a-stabilizer-code.md)
- [The five-qubit code is a nondegenerate $[[5, 1, 3]]$ code](../small-stabilizer-codes/five-qubit-code-is-a-nondegenerate-5-1-3-code.md)
- [Shor's code has distance three](../bit-flip-and-shor-codes/shor-codeword-distance-three.md)

## Sources

- Y.-J. Wang, B. Zeng, M. Grassl and B. C. Sanders, *Stabilizer formalism for generalized concatenated quantum codes*, Proceedings of the 2013 IEEE International Symposium on Information Theory, 529–533, arXiv:1309.5598, Section II.A, equation (1) (the concatenated code $A \circ B$ of an outer $[[N, K, D]]$ and an inner $[[n, k, d]]$ code, obtained by encoding each outer qudit into the inner code, is an $[[nN, kK, D']]$ code with $D' \ge dD$).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.5 ("The result is an $[n_1 n_2, k, d_1 d_2]$ code").
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.15.1, equations (7.204)–(7.206).
- A. R. Calderbank, E. M. Rains, P. W. Shor and N. J. A. Sloane, *Quantum error correction via codes over GF(4)*, IEEE Trans. Inform. Theory 44 (1998), 1369–1387, arXiv:quant-ph/9608006, Section 4, the paragraph after Theorem 8 ("an $[[nn_2, k, dd_2]]$ concatenated code").
