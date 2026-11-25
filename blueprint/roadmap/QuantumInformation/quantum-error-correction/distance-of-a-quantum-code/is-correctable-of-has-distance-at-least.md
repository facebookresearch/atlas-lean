# A code of distance $2t + 1$ corrects $t$ errors

Let $P$ be an orthogonal projector onto a code on $n$ qubits with
[distance at least $d$](has-distance-at-least.md). Then the set of Pauli errors $X^a Z^b$ whose
[weight](pauli-weight.md) $t$ satisfies $2t + 1 \le d$ is
[correctable](../knill-laflamme-conditions/is-correctable.md) on the code, by a single recovery
channel. This is Preskill's statement in Section 7.3.1: "a QECC with distance $d = 2t + 1$ can
correct $t$ errors".

Proof: for two such errors, $(X^a Z^b)^{*} X^{a'} Z^{b'}$ is
[up to a sign](conj-transpose-pauli-mul-pauli.md) the Pauli operator $X^{a + a'} Z^{b + b'}$,
whose weight is [at most](pauli-weight-add-le.md) $2t < d$. So
$P (X^a Z^b)^{*} X^{a'} Z^{b'} P$ is a multiple of $P$, and the
[sufficiency of the Knill–Laflamme conditions](../knill-laflamme-conditions/is-correctable-of-knill-laflamme.md)
gives the recovery channel.

The hypothesis is satisfiable, for instance by the one-dimensional code spanned by $|00\rangle$ with
$d = 3$, for which every single-qubit Pauli error is correctable.

## Informally uses

- [Product of two Pauli operators](conj-transpose-pauli-mul-pauli.md): reduces $E_a^{*} E_b$ to one Pauli operator.
- [Weight of a product of Pauli operators](pauli-weight-add-le.md): bounds its weight by $2t$.
- [Sufficiency of the Knill–Laflamme conditions](../knill-laflamme-conditions/is-correctable-of-knill-laflamme.md): builds the recovery.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.3.1, equations (7.34)–(7.35).
- E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, Phys. Rev. A 55 (1997), 900–911, arXiv:quant-ph/9604034, Theorem 3.2.
