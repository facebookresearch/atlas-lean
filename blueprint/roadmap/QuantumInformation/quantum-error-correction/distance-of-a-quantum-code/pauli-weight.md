# Weight of a Pauli operator

The weight of the Pauli operator $X^a Z^b$ on $n$ qubits ($a, b \in \mathbb{F}_2^n$) is

$$\operatorname{wt}(a, b) = \#\{ i : a_i \ne 0 \text{ or } b_i \ne 0 \},$$

the number of qubits on which it acts by a nontrivial Pauli matrix $X$, $Z$ or $XZ$. Preskill
defines it for the strings in $\{I, X, Y, Z\}^{\otimes n}$: "the weight is the number of qubits
acted on by a nontrivial Pauli matrix". The same count appears in the statement that
[CSS codes correct $\lfloor (d-1)/2 \rfloor$ errors](../css-codes/is-correctable-css.md).

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.2, after equation (7.13).
