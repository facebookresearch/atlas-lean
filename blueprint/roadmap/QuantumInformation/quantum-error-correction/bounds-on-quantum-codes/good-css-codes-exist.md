# Good CSS codes exist

Let $H_2(x) = -x \log_2 x - (1 - x) \log_2 (1 - x)$. For every $\delta$ with $0 < \delta < 1/2$ and $H_2(\delta) < 1/2$, and
every $\varepsilon > 0$, for all sufficiently large even $n$ there is a binary linear code $C \subseteq \mathbb{F}_2^n$ with
$1^n \in C \subseteq C^{\perp}$ such that $C^{\perp}$ has minimum distance at least $\delta n$ and

$$\frac{n - 2 \dim C}{n} \;\ge\; 1 - 2 H_2(\delta) - \varepsilon .$$

The CSS code $Q_{C^{\perp}, C}$ then encodes $n - 2\dim C$ qubits into $n$ and
[corrects $\lfloor (\delta n - 1)/2 \rfloor$ errors](../css-codes/is-correctable-css.md), since both $C_1 = C^{\perp}$ and
$C_2^{\perp} = C^{\perp}$ have minimum distance at least $\delta n$. So there are families of quantum codes whose rate and
relative number of correctable errors both stay bounded away from $0$. The lengths must be even: $1^n \in C^{\perp}$ means
$1^n \cdot 1^n = n \equiv 0 \pmod 2$.

## Expansion

A good expansion adds pages for the two counting steps of Calderbank and Shor's proof: the greedy lemma (their Lemma 3):
a family of $[n_i, k_i]$ codes with $k_i/n_i > R$ in which every nonzero word lies in the same number of codes contains
codes meeting the Gilbert–Varshamov bound, applied here inside the even-weight words with $1^n$ set aside, since $1^n$
lies in every $C^{\perp}$ and odd-weight words lie in none; and the count needed for the dual distance, from MacWilliams,
Sloane and Thompson (Theorem 2.1 there): for an even-weight word $v$ outside the span of $1^n$, the number of
$k$-dimensional weakly self-dual codes $C$ with $v \in C^{\perp}$, equivalently $C \subseteq v^{\perp}$, does not depend
on $v$.

## Depends on

- [CSS codes correct $\lfloor (d - 1) / 2 \rfloor$ errors](../css-codes/is-correctable-css.md)
- [Linear code](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md)
- [Dual code](../../../InformationTheory/error-correcting-codes/linear-codes/dual.md)

## Sources

- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Abstract and Section V, Lemma 3 and equations (27)–(30) (the tower $\langle 1^n \rangle \subseteq C \subseteq C^{\perp}$ and the count of weakly self-dual codes contained in $v^{\perp}$ for even-weight $v$).
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.14 (good codes).
