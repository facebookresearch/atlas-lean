# Equivalence of erasing pattern languages with length constraints is undecidable

No algorithm decides whether two patterns whose variables are subject to linear constraints on their substitution lengths generate the same
erasing pattern language, even for patterns without letters and constraints without disjunctions.

Use [pattern languages](pattern-languages-with-regular-constraints.md) over a finite alphabet $\Sigma$. A *length constraint* is a disjunction of systems of linear Diophantine inequalities over variables; a *pattern with length
constraints* is a pair $(\alpha, \ell_\alpha)$ of a pattern and a length constraint on variables of $\alpha$. A substitution $h$ is *$\ell_\alpha$-valid* if the lengths $|h(x)|$ satisfy $\ell_\alpha$, and the erasing and non-erasing languages
$L_E(\alpha, \ell_\alpha)$ and $L_{NE}(\alpha, \ell_\alpha)$ collect the words $h(\alpha)$ over $\ell_\alpha$-valid substitutions $h$, non-erasing ones for $L_{NE}$. Patterns may carry regular and length constraints together.

The inequalities have integer coefficients and their unknowns, one for each variable $x$ of the pattern, stand for the lengths $|h(x)| \in \mathbb{N}$; the alphabet $\Sigma$ is fixed, and an instance consists of the patterns with their constraints, regular constraints being given by finite automata.

**Theorem (Nowotka and Wiedenhöft).** For every alphabet $\Sigma$ with $|\Sigma| \ge 2$:

1. it is undecidable, given patterns with length constraints $(\alpha, \ell_\alpha)$ and $(\beta, \ell_\beta)$, whether $L_E(\alpha, \ell_\alpha) = L_E(\beta, \ell_\beta)$, even when $\alpha$ and $\beta$ are terminal-free and $\ell_\alpha, \ell_\beta$ contain no disjunction (Theorem 8 of the source; the proof reduces emptiness of nondeterministic two-counter automata);
2. inclusion $L_{NE}(\alpha, \ell_\alpha) \subseteq L_{NE}(\beta, \ell_\beta)$ is undecidable for terminal-free patterns with length constraints, even without disjunctions (Theorem 12);
3. it is undecidable, given patterns with regular and length constraints, whether their non-erasing languages are equal, even for terminal-free patterns (Theorem 19).

Equivalence of erasing pattern languages without constraints is a long-standing open problem, while for non-erasing ones it is trivially decidable; item 1 shows that length constraints, like regular constraints, make the erasing
case undecidable. Membership stays NP-complete with length constraints.

## Depends on

- [Pattern languages with regular constraints](pattern-languages-with-regular-constraints.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Items 1 and 3 reduce emptiness of nondeterministic two-counter automata without input, adapting the inclusion constructions of Jiang et al. and of Freydenberger and Reidenbach: the two constrained patterns are built so that one language always
contains the other and they differ exactly on encodings of accepting computations of the automaton. Item 2 adapts the construction of Bremer and Freydenberger, which uses a specific universal Turing machine, to
terminal-free patterns for alphabets with at least three letters; the binary case follows from Saarela's theorem that inclusion of terminal-free non-erasing pattern languages is undecidable. A complete expansion links Saarela's theorem and the
Bremer–Freydenberger inclusion theorem.

## Sources

- D. Nowotka and M. Wiedenhöft, "The equivalence problem of E-pattern languages with length constraints is undecidable", in *36th Annual Symposium on Combinatorial Pattern Matching (CPM 2025)*, LIPIcs 331, paper 4, 2025, doi:10.4230/LIPIcs.CPM.2025.4; read in arXiv:2411.06904v2: the main theorem on erasing equivalence, the theorem on terminal-free non-erasing inclusion and the theorem on non-erasing equivalence with regular and length constraints, stated in Sections 3 and 4 and proved in the appendices, with the membership corollary of Section 3. Theorem numbers are not cited because the version read numbers its appendix first.
