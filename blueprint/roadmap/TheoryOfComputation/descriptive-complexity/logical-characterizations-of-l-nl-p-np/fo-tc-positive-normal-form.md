# Immerman: FO(TC) collapses to positive transitive closure

On ordered finite structures, every FO(TC) sentence is equivalent to one in which the transitive-closure operator occurs only positively (indeed to a single application $\mathrm{TC}[\varphi](\bar 0,\overline{\max})$ with $\varphi$ first-order, and even quantifier-free when the successor relation is a built-in symbol). Hence FO(TC) and FO(positive TC) both capture $\mathsf{NL}$, and FO(TC) model checking for a fixed sentence is in $\mathsf{NL}$, negated closures being evaluated by inductive counting.

## Proof sketch

FO(posTC) $\subseteq$ NL by guessing paths; NL $\subseteq$ FO(posTC) via the NL-completeness of REACH under first-order reductions. Negated closures are in NL by the inductive counting of Immerman–Szelepcsényi, so FO(TC) $\subseteq$ NL as well, and the collapse follows from the capture theorem.

## Depends on

- [Formulas of first-order logic with transitive closure](../transitive-closure-logic-and-nl/tcfo.md)
- [Canonically ordered structures with BIT](../ordered-structures-and-arithmetic/canonically-ordered-structures-with-bit.md)
- [The complexity class NL](../../complexity-classes/time-and-space-complexity-classes/nl.md)

## Proof depends on

- [Immerman: REACH is NL-complete under first-order reductions](reach-nl-complete-first-order.md)
- [Immerman-Szelepcsenyi theorem: NL = coNL](../../complexity-classes/immerman-szelepcsenyi.md)
- [Immerman: FO + transitive closure is NL on ordered structures](../transitive-closure-logic-and-nl/fo-tc-eq-nl.md)

## Sources

- Neil Immerman, "Languages That Capture Complexity Classes", SIAM Journal on Computing 16(4), 760–778, 1987: Theorem 3.1 (NL = FO(pos TC)), Theorems 3.3 and 3.7 (the single-closure normal form, first-order and quantifier-free with successor).
- Neil Immerman, "Nondeterministic Space Is Closed under Complementation", SIAM Journal on Computing 17(5), 935–938, 1988, Corollary 3.
