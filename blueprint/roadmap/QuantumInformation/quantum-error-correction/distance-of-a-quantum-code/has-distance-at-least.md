# Distance of a quantum code (lower bound)

Let $P$ be the projector onto a code on $n$ qubits. The code has distance at least $d$ if every
Pauli operator $X^a Z^b$ of [weight](pauli-weight.md) less than $d$ satisfies

$$P X^a Z^b P = c_{a,b} \, P$$

for some scalar $c_{a,b}$. In an orthonormal basis $|\bar\imath\rangle$ of the code this is
$\langle \bar\imath | X^a Z^b | \bar\jmath \rangle = c_{a,b} \delta_{ij}$. Preskill defines the
distance $d$ as the minimum weight of a Pauli operator $E$ with
$\langle \bar\imath | E | \bar\jmath \rangle \ne C_E \delta_{ij}$ (equation (7.34)), so the code
has distance at least $d$ in the sense here exactly when its distance is at least $d$ in his.
The definition records a lower bound because the exact distance is a minimum that may not exist:
a one-dimensional code satisfies the condition for every $d$.

Preskill states the definition for Pauli strings in $\{I, X, Y, Z\}^{\otimes n}$; the operators
$X^a Z^b$ are the same operators up to the phases $\pm 1, \pm i$, which do not affect the
condition.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.3.1, equation (7.34).
