# ω-visibly pushdown languages are closed under complement but not determinizable

An *$\omega$-VPA* is a [visibly pushdown automaton](visibly-pushdown-automata.md) read on infinite words, with runs defined as for finite words and either a
Büchi condition (some state of $F$ occurs infinitely often) or a Muller condition (the set of states occurring infinitely often belongs to a
given family); the languages accepted by nondeterministic Büchi $\omega$-VPAs are the *$\omega$-VPLs*. Over a fixed pushdown alphabet they are closed under union, intersection,
renaming to another pushdown alphabet (with respect to the image alphabet) that maps calls to calls, returns to returns and local actions to local actions, prefixing by a VPL and $\omega$-iteration of a VPL, and under complement. Unlike the finite-word case they cannot be determinized:
the language $L_{\mathrm{repbdd}}$ of infinite words over one call $c$ and one return $r$ that are *repeatedly bounded* (for some $n$ the stack depth is at
most $n$ infinitely often) is accepted by a nondeterministic Büchi $\omega$-VPA but by no deterministic Muller $\omega$-VPA. Complementation goes
through a factorization of the word into pending letters and well-matched blocks, summarized by a finite-state abstraction.

## Depends on

- [Visibly pushdown automata and visibly pushdown languages](visibly-pushdown-automata.md)
- [Büchi acceptance condition](../../omega-automata-and-games/emptiness-of-b-chi-automata/mem-language-iff.md)

## Proof depends on

- [Büchi automata are closed under complementation](../../omega-automata-and-games/boolean-closure-of-b-chi-automata/exists-buchi-compl.md)

## Sources

- R. Alur and P. Madhusudan, "Visibly pushdown languages", *Proceedings of the 36th ACM STOC*, 2004; full version of August 2005, whose numbering is cited, <https://www.cis.upenn.edu/~alur/Stoc04.pdf>: Section 6, the definition of $\omega$-VPAs with Büchi and Muller conditions, Theorem 7 (closure), the language $L_{\mathrm{repbdd}}$ and Theorem 8 (deterministic versus nondeterministic $\omega$-VPAs), and Theorem 9 (complementability) with its proof.
