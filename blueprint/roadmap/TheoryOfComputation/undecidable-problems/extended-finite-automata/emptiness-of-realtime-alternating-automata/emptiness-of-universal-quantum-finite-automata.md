# Emptiness of universal quantum finite automata is undecidable

No algorithm decides, given a quantum finite automaton with rational amplitudes, whether some input word is accepted with probability exactly 1.

**Theorem.** The emptiness problem for universal quantum finite automata (UQFAs, see [alternating quantum finite automata](alternating-quantum-finite-automata.md)) whose operation elements have rational entries is undecidable: there is no algorithm that, given such a QFA $M$, decides whether there is a word $w$ with $f_M(w)=1$.

By contrast, emptiness for nondeterministic QFAs (is there $w$ with $f_M(w)>0$?) is decidable for algebraic amplitudes (Theorem 4.1 of the source).

## Depends on

- [Alternating quantum finite automata](alternating-quantum-finite-automata.md)

## Proof depends on

None.

## Expansion

A UQFA accepts $w$ when $f_M(w)=1$, so emptiness asks whether the value $1$ is attained. The source derives this from the known undecidability of the question, for a QFA $M$ with rational amplitudes and a value $p\in[0,1]$, whether some word is accepted with probability exactly $p$; the source attributes this, already for measure-once (Moore–Crutchfield) quantum automata, to work of Derksen, Jeandel and Koiran and of Blondel, Jeandel, Koiran and Portier.

## Sources

- H. Gökalp Demirci, Mika Hirvensalo, Klaus Reinhardt, A. C. Cem Say and Abuzer Yakaryılmaz, "Alternating, private alternating, and quantum alternating realtime automata", *Logical Methods in Computer Science* 15(3), 2019, paper 22, doi:[10.23638/LMCS-15(3:22)2019](https://doi.org/10.23638/LMCS-15(3:22)2019); numbering of arXiv:1407.0334v5 ([arXiv](https://arxiv.org/abs/1407.0334v5)): Corollary 4.2 and the paragraph before it.
