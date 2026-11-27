# Equivalence and rationality of pomset automata are undecidable

For finite pomset automata without further restrictions, no algorithm decides whether two states accept the same pomset
language, and none decides whether the language of a state is series-parallel rational.

Let $A$ range over finite [pomset automata](pomset-automata-and-series-parallel-rational-lan.md).

**Theorem.** The following problems are undecidable:

1. given a finite PA $A$ and states $q, q'$ of $A$, does $L_A(q) = L_A(q')$ hold?
2. given a finite PA $A$ and a state $q$ of $A$, is $L_A(q)$ an spr-language?

The second result explains why the Kleene theorem of the source needs the restriction to well-nested pomset automata: without
it, finiteness of the automaton does not guarantee a rational language, and rationality cannot even be decided.

## Depends on

- [Pomset automata and series-parallel rational languages](pomset-automata-and-series-parallel-rational-lan.md)

## Proof depends on

- [Equivalence of context-free grammars is undecidable](../../undecidable-problems/undecidable-problems-for-context-free-grammars/exists-not-tm2-decidable-language-eq.md)
- [Regularity of context-free languages is undecidable](../../undecidable-problems/regularity-problem-for-context-free-languages/exists-not-tm2-decidable-is-regular.md)

## Expansion

Finite pomset automata accept exactly the pomset languages of context-free pomset grammars: a finite automaton gives a grammar
with one nonterminal per state, and a grammar is turned into an automaton whose states are its nonterminals and the subterms of
its rules, with $\delta(a, a) = \top$ and $\gamma$ splitting parallel and sequential subterms. Ordinary context-free grammars
on words are context-free pomset grammars without parallel products, so the classical undecidable problems for context-free
grammars (Bar-Hillel, Perles and Shamir; Greibach) carry over to pomset automata; the source records the two problems above as
a corollary of this correspondence.

## Sources

- T. Kappé, P. Brunet, B. Luttik, A. Silva and F. Zanasi, "On series-parallel pomset languages: rationality, context-freeness and automata", *Journal of Logical and Algebraic Methods in Programming* 103:130–153, 2019, doi:10.1016/j.jlamp.2018.12.001; Corollary 6.2 of the version arXiv:1812.03058v2, with Theorem 6.1 and its proof.
