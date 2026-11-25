# The sets-as-trees model of ZFC in type theory

This node covers sets constructed, after Aczel, in the calculus of inductive constructions, a
dependent type theory with an impredicative sort of propositions and a hierarchy of universes, as
well-founded trees modulo extensional equivalence, and the statement that, with membership, they form
a model of the axioms of Zermelo–Fraenkel set theory with choice, read as sentences of the
first-order language with one binary relation symbol $\in$. A set is given by a type $A$ in a universe
and a family of sets indexed by $A$, the set of the members of the family; two sets are equal when
every member of each is equal to some member of the other, and a set belongs to another when it is
equal to one of its members. Extensionality holds by this definition of equality, and there are an
empty set, pairs, unions, subsets defined by separation by any proposition, power sets, which use the
impredicative sort of propositions, and a set of natural numbers containing $\emptyset$ and closed
under $n \mapsto n \cup \{n\}$. With excluded middle added to the host, these give the axioms of
Zermelo set theory, and regularity follows from $\in$-induction (structural induction on trees) with
excluded middle. Replacement, for functional predicates, needs in addition a type-theoretic
description axiom (a choice principle on types), and the axiom of choice a further type-theoretic
choice axiom compatible with extensional equality. The axioms then hold as theorems of the host type
theory with excluded middle and these two axioms; this gives the consistency of ZFC relative to that
type theory and is not a proof inside ZFC of the consistency of ZFC.

## Background

- [Axiomatic set theory and models of ZFC](README.md)

## Expansion

A sound expansion fixes the host type theory and its principles (the impredicative sort of
propositions, the universe levels used, excluded middle and the two type-theoretic axioms), the
first-order language of set theory, the axioms of ZFC as a set of sentences with the separation and
replacement schemata stated with parameters and one chosen form of choice, and the structure of these
sets with membership. It then has separate pages for each axiom or schema holding in that structure,
translating set operations of the host into first-order satisfaction (separation and replacement for
every first-order formula with parameters, not only for predicates or functions of the host), and for
the statement that the structure is a model of ZFC. Images of sets under functions of the host are
defined only for functions that respect extensional equality. That every function of the host is
admissible for replacement, which uses the host's choice, is not first-order definability and must
not replace the replacement schema. In Aczel's original, predicative setting (Martin-Löf type
theory) the construction interprets constructive set theory instead; that is a separate statement.

## Sources

- B. Werner, "Sets in types, types in sets", in *Theoretical Aspects of Computer Software (TACS '97)*,
  LNCS 1281, Springer, 1997, Section 4 (sets as trees after Aczel, equality and membership, pairs,
  empty set, union, separation, power set, natural numbers, replacement and choice; Definitions 12
  and 14, Theorems 17–19). <http://www.lix.polytechnique.fr/Labo/Benjamin.Werner/publis/tacs97.pdf>
