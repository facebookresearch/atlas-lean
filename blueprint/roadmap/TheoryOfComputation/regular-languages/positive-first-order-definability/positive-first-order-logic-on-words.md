# Positive first-order logic on words

Positive first-order logic on words over an ordered alphabet is the negation-free first-order logic whose letter predicates hold at positions carrying the given letter or a larger one; the languages it defines are monotone, that is, closed under raising letters.

Let $A$ be a finite alphabet with a partial order $\le_A$, extended to words of equal length letter by letter: $a_1\cdots a_n\le_A b_1\cdots b_m$ iff $n=m$ and $a_i\le_A b_i$ for all $i$. A *powerset alphabet* is $A=\mathcal P(P)$ for a finite set $P$ of predicates, ordered by inclusion. A language $L\subseteq A^*$ (of finite words) is *monotone* if $u\in L$ and $u\le_A v$ imply $v\in L$; its *monotone closure* is $\{v:\exists u\in L,\ u\le_A v\}$. For $a\in A$ let ${\uparrow}a=\{b\in A: a\le_A b\}$.

The formulas of *positive first-order logic* $\mathrm{FO}^+$ are

$$
\varphi,\psi ::= {\uparrow}a(x)\mid x\le y\mid x<y\mid \varphi\vee\psi\mid\varphi\wedge\psi\mid\exists x.\varphi\mid\forall x.\varphi,
$$

with variables ranging over the positions of a word $u$; ${\uparrow}a(x)$ is true when $a\le_A u[x]$, and the other constructs have their usual meaning. A sentence $\varphi$ defines $\{u\in A^*: u\models\varphi\}$, and a language is *$\mathrm{FO}^+$-definable* if some sentence defines it. Every $\mathrm{FO}^+$-definable language is monotone and first-order definable. Over a powerset alphabet, $\mathrm{FO}^+$ is the negation-free fragment of first-order logic with one unary predicate per element of $P$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Monotone first-order definable languages need not be $\mathrm{FO}^+$-definable: the source exhibits a regular, first-order definable, monotone language that is not $\mathrm{FO}^+$-definable, the word analogue of the failure of Lyndon's positivity theorem on finite structures. Definability is studied with an ordered variant of Ehrenfeucht–Fraïssé games.

## Sources

- Denis Kuperberg, "Positive First-order Logic on Words and Graphs", *Logical Methods in Computer Science* 19(3), 2023, paper 7, doi:[10.46298/lmcs-19(3:7)2023](https://doi.org/10.46298/lmcs-19(3:7)2023); numbering of arXiv:2201.11619v5 ([arXiv](https://arxiv.org/abs/2201.11619v5)): Section 2 (ordered and powerset alphabets, monotone languages, Definitions 2.1 and 2.3) and Section 3.1 (syntax and semantics of $\mathrm{FO}^+$).
