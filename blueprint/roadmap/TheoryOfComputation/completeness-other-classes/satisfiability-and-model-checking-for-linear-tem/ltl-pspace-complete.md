# Satisfiability, validity and model checking of LTL are PSPACE-complete

Each of the three decision problems below, with the formula given by its linear-size token
encoding, is in PSPACE, and every problem in PSPACE reduces to it by a polynomial-time
many-one reduction:

- [satisfiability](ltl-sat-dec.md): some infinite word over sets of atoms satisfies the formula;
- [validity](ltl-valid-dec.md): every such word satisfies it;
- [model checking](ltl-model-check-dec.md): every infinite path from the start world of a finite
  total Kripke structure satisfies it.

For model checking this is the combined complexity, with both the structure and the formula in
the input. Vardi's Theorem 25 states the specification complexity (the structure fixed) is
PSPACE-complete and gives the space bound $O((|\varphi| + \log |P|)^2)$; together these give the
combined statement. The upper bounds come from the automata-theoretic approach: the Büchi
automaton of a formula has $2^{O(|\varphi|)}$ states and its nonemptiness, alone or in product
with the structure, is tested on the fly in nondeterministic polynomial space, then Savitch's
theorem applies.

## Background

- [LTL satisfiability is Büchi nonemptiness](../../../Logic/temporal-logic/model-checking-for-linear-temporal-logic/satisfiable-iff-language-ne-bot.md):
  the reduction behind the upper bound for satisfiability.
- [Vardi–Wolper translation with an exponential state bound](../../../Logic/temporal-logic/model-checking-for-linear-temporal-logic/exists-buchi-card-le.md):
  the exponential automaton.
- [The model checking, satisfiability and validity problems of the linear modal μ-calculus are PSPACE-complete](../satisfiability-and-model-checking-for-the-linear/linear-mu-calculus-pspace-complete.md):
  the same result for the linear-time μ-calculus, stated in the same format.

## Sources

- Moshe Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 4, Theorems 24 and 25.
- A. Prasad Sistla and Edmund M. Clarke, "The complexity of propositional linear temporal logics",
  *J. ACM* 32 (1985), 733-749.
