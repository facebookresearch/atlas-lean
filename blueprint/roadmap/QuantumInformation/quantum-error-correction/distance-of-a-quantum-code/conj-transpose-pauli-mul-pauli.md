# Product of two Pauli operators

For $a, b, a', b' \in \mathbb{F}_2^n$,

$$(X^a Z^b)^{*} \, X^{a'} Z^{b'} = (-1)^{b \cdot (a + a')} \, X^{a + a'} Z^{b + b'}.$$

So the product of two Pauli operators is a Pauli operator up to a sign, as in Preskill's
description of the Pauli group $G_n$ (Section 7.9.1). Taking $a' = a$, $b' = b$ gives
$(X^a Z^b)^{*} X^a Z^b = I$: each $X^a Z^b$ is unitary (property (i) there).

The proof compares entries: $(X^a Z^b)_{uv} = [u = v + a]\,(-1)^{b \cdot v}$, so the product has
entry $[u + a = v + a'](-1)^{b \cdot u + b' \cdot v}$, and $u = v + a + a'$ turns the exponent
into $(b + b') \cdot v + b \cdot (a + a')$.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.9.1, properties (i)–(iv) of the Pauli group.
