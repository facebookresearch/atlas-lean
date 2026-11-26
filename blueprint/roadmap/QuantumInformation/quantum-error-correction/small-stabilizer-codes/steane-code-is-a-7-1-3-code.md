# Steane's code is a $[[7, 1, 3]]$ code

[Steane's seven-qubit code](steane-seven-qubit-code.md) is a nondegenerate $[[7, 1, 3]]$ code: it has dimension $2$,
every Pauli operator of weight at most $2$ satisfies the distance condition, and some operator of weight $3$, for
instance $X_1 X_2 X_3$ (as $1110000$ is an odd-weight word of $C$), does not. Hence it corrects an arbitrary error on any one of the seven
qubits.

Proof: by the [distance formula for CSS codes](../css-codes/distance-of-a-css-code.md) with $C_1 = C$ and
$C_2 = C^{\perp}$, the distance is the least weight of a word in $C \setminus C^{\perp}$, the odd-weight Hamming
codewords, which is $3$ by the [minimum distance of the Hamming code](../../../InformationTheory/error-correcting-codes/hamming-7-4-code/min-dist-code.md).
Every element of the stabilizer other than $I$ has weight at least $4$, the least weight of a nonzero word of
$C^{\perp}$, so the code is nondegenerate.

## Depends on

- [Steane's seven-qubit code](steane-seven-qubit-code.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)
- [Degenerate quantum code](../distance-of-a-quantum-code/degenerate-quantum-code.md)

## Proof depends on

- [Distance of a CSS code](../css-codes/distance-of-a-css-code.md)
- [Minimum distance of the Hamming (7,4) code](../../../InformationTheory/error-correcting-codes/hamming-7-4-code/min-dist-code.md)

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.7.
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.3 (the seven-qubit CSS code, Table 3.4).
