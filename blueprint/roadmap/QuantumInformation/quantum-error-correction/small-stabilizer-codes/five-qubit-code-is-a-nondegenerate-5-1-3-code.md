# The five-qubit code is a nondegenerate $[[5, 1, 3]]$ code

The [five-qubit code](five-qubit-code.md) is a nondegenerate $[[5, 1, 3]]$ code. Every Pauli operator of weight $1$ or
$2$ anticommutes with at least one of $M_1, \dots, M_4$; the operator $Y_1 Z_2 Y_3$ commutes with the stabilizer
without lying in it; and every element of the stabilizer other than $I$ has weight $4$. By the
[quantum Singleton bound](../distance-of-a-quantum-code/quantum-singleton-bound.md), $n \ge 5$ for any code with
$k = 1$ and $d = 3$, so the five-qubit code is the shortest code encoding one qubit that corrects an arbitrary
single-qubit error.

Proof: the weight-$1$ and weight-$2$ cases are a finite check of [syndromes](../stabilizer-formalism/error-syndrome.md)
(for example, a weight-$2$ operator on qubits $1, 2$ commuting with $M_2$ and $M_3$ must be $X_1 X_2$ up to a phase, which anticommutes with $M_1$);
the [correctability criterion](../stabilizer-codes-correctability-criterion-and-distance.md) then gives distance at
least $3$, and $Y_1 Z_2 Y_3 \in N(S) \setminus \langle iI \rangle S$ gives distance exactly $3$.

## Depends on

- [The five-qubit code](five-qubit-code.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)
- [Degenerate quantum code](../distance-of-a-quantum-code/degenerate-quantum-code.md)

## Proof depends on

- [Stabilizer codes: correctability criterion and distance](../stabilizer-codes-correctability-criterion-and-distance.md)
- [Error syndrome of a stabilizer code](../stabilizer-formalism/error-syndrome.md)
- [The quantum Singleton bound](../distance-of-a-quantum-code/quantum-singleton-bound.md)
- [A code of distance $2t + 1$ corrects $t$ errors](../distance-of-a-quantum-code/is-correctable-of-has-distance-at-least.md)
- [Correctable errors form a linear space](../knill-laflamme-conditions/is-correctable-of-forall-mem-span.md)

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.10, equations (7.148)–(7.151).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.3 ("It has distance three (for instance, $\sigma_{y1} \sigma_{z2} \sigma_{y3} \in N(S) - S$) and is nondegenerate").
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 2.2, the remark after equation (38).
