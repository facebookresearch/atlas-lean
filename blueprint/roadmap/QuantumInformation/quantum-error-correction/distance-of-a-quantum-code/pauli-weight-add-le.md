# Weight of a product of Pauli operators

The Pauli operator $X^{a + a'} Z^{b + b'}$, which is the
[product](conj-transpose-pauli-mul-pauli.md) of $X^a Z^b$ and $X^{a'} Z^{b'}$ up to a sign, has
[weight](pauli-weight.md) at most the sum of their weights:

$$\operatorname{wt}(a + a', b + b') \le \operatorname{wt}(a, b) + \operatorname{wt}(a', b').$$

It acts trivially on every qubit where both factors act trivially, so its support is contained
in the union of their supports. This is the step "$E_a^{\dagger} E_b$ has weight at most $2t$"
in Preskill's argument that a distance-$(2t + 1)$ code corrects $t$ errors.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.3.1.
