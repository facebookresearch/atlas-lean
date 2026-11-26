# A code of distance $d$ corrects $d - 1$ erasures

Let $P$ be the orthogonal projector onto a code on $n$ qubits with [distance at least $d$](has-distance-at-least.md),
and let $L \subseteq \{1, \dots, n\}$ be a set of at most $d - 1$ positions. Then the family of all Pauli operators
$X^a Z^b$ supported in $L$ ($a_i = b_i = 0$ for $i \notin L$) is [correctable](../knill-laflamme-conditions/is-correctable.md)
on the code, by one recovery channel depending on $L$. By linearity this recovers every error acting only on the known
positions $L$, such as qubits that were lost and replaced: a code of distance $d$ corrects $d - 1$ erasures, and a code
correcting $t$ errors at unknown positions corrects $2t$ erasures.

Proof: for two such errors, $(X^a Z^b)^{*} X^{a'} Z^{b'}$ is, up to a sign, $X^{a + a'} Z^{b + b'}$, which is supported in
$L$ and so has weight at most $d - 1$; the distance condition then gives the Knill–Laflamme conditions, and their
sufficiency gives the recovery. For the last
clause, a code that corrects every error on at most $t$ unknown qubits has distance at least $2t + 1$: a Pauli operator of
weight at most $2t$ is, up to a phase, a product $E_1^{*} E_2$ of two Pauli operators of weight at most $t$ with disjoint
supports, and the necessity of the Knill–Laflamme conditions for $\{E_1, E_2\}$ gives $P E_1^{*} E_2 P \in \mathbb{C} P$.

## Depends on

- [Distance of a quantum code (lower bound)](has-distance-at-least.md)
- [Correctable errors on a quantum code](../knill-laflamme-conditions/is-correctable.md)
- [Pauli operator $X^a Z^b$ on $n$ qubits](../css-codes/pauli.md)
- [Weight of a Pauli operator](pauli-weight.md)

## Proof depends on

- [Necessity of the Knill–Laflamme conditions](../knill-laflamme-conditions/knill-laflamme-of-is-correctable.md)
- [Product of two Pauli operators](conj-transpose-pauli-mul-pauli.md)
- [Sufficiency of the Knill–Laflamme conditions](../knill-laflamme-conditions/is-correctable-of-knill-laflamme.md)
- [Correctable errors form a linear space](../knill-laflamme-conditions/is-correctable-of-forall-mem-span.md)

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.3.2.
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 2.3, the paragraph on located errors.
- M. Grassl, Th. Beth and T. Pellizzari, *Codes for the quantum erasure channel*, Phys. Rev. A 56 (1997), 33–38, arXiv:quant-ph/9610042, Section III.A of the journal article (the conditions on codes for the erasure channel, including the converse that correcting $t$ errors gives correction of $2t$ erasures; numbered differently in the arXiv version).
