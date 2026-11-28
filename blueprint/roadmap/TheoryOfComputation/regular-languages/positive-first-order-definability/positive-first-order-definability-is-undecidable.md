# Positive first-order definability of regular languages is undecidable

No algorithm decides, given a regular language over a powerset alphabet, whether it is definable in positive first-order logic.

**Theorem.** The following problem is undecidable: given a regular language $L$ of finite words over a powerset alphabet $A=\mathcal P(P)$ (for instance by a finite automaton), is $L$ definable in [positive first-order logic](positive-first-order-logic-on-words.md)?

Since first-order definability of regular languages is decidable, the problem is equally undecidable when $L$ is given by a first-order sentence. Undecidability on powerset alphabets implies undecidability on general ordered alphabets.

## Depends on

- [Positive first-order logic on words](positive-first-order-logic-on-words.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the mortality problem for Turing machines, undecidable by Hooper's theorem as the source recalls: a deterministic machine is *mortal* if there is $n$ such that from every finite configuration it halts within $n$ steps. From $M$ one builds an ordered alphabet and a regular language $C=C_1\cup C_2\cup C_3$ of configuration words of three types, ordered so that two configuration words encoding successive configurations of the same length have a common upper bound (Lemma 6.5 of the source), and two configuration words with a common upper bound are equal or encode successive configurations (Lemma 6.6). The language $L_M$ is essentially the monotone closure of $(C_1\#C_2\#C_3\#)^*$. If $M$ is not mortal, arbitrarily long runs give pairs $u\in L_M$, $v\notin L_M$ on which Duplicator wins the ordered Ehrenfeucht–Fraïssé game of every length, so $L_M$ is not $\mathrm{FO}^+$-definable. If every run has length at most $n$, Spoiler wins in a number of rounds depending only on $n$, through an abstract integer game on configuration heights, so $L_M$ is $\mathrm{FO}^+$-definable. A good expansion links pages for the undecidability of mortality of Turing machines (Hooper) and for the ordered Ehrenfeucht–Fraïssé game characterization of $\mathrm{FO}^+$-definability.

## Sources

- Denis Kuperberg, "Positive First-order Logic on Words and Graphs", *Logical Methods in Computer Science* 19(3), 2023, paper 7, doi:[10.46298/lmcs-19(3:7)2023](https://doi.org/10.46298/lmcs-19(3:7)2023); numbering of arXiv:2201.11619v5 ([arXiv](https://arxiv.org/abs/2201.11619v5)): Theorem 6.1 and its proof in Section 6.
