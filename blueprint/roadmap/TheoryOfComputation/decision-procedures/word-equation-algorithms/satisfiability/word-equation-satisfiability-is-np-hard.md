# Satisfiability of unary word-equation systems is NP-hard

Deciding whether a system of word equations over a one-letter alphabet has a solution is NP-hard, even when both sides of every equation are nonempty. Solutions may erase variables.

The following decision problem on bitstrings is NP-hard, that is, every decision problem in NP has a polynomial-time many-one reduction to it. Given a finite variable alphabet $\mathcal{X}$ and a finite system of word equations over the constant alphabet $\{a\}$, each with two nonempty sides, decide whether it has a solution $\sigma : \mathcal{X} \to a^*$. Equation sides are written out explicitly; symbols and variable identifiers use binary codes in the canonical encoding, and malformed encodings are rejected.

Saarela's unary problem $\mathrm{EqSat}(?,1)$ is the sourced main result here. The fixed-binary single-equation restriction is a derived consequence explained in Expansion, not a second source-stated main result.

For general word equations, the cited sources give NP-hardness as the best lower bound and leave membership in NP open; their best upper bound is [nondeterministic linear space](word-equation-satisfiability-in-nondeterministic-linear-space.md), in particular [PSPACE](word-equation-satisfiability-in-pspace.md).


## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [EXACT COVER BY 3-SETS is NP-complete](../../../np-completeness/set-systems-and-location/exact-cover-by-3-sets/exact-cover-by3-sets-np-complete.md)
- [NP-hardness transfers along reductions](../../../np-completeness/satisfiability/3-satisfiability/np-hard-of-poly-many-one-red.md)

## Expansion

Saarela, Section 2, pp. 140:4–6, defines patterns as nonempty words and equations as pairs of patterns, allows erasing solutions, and states that $\mathrm{EqSat}(?,1)$ is equivalent to linear integer programming in unary notation, which is NP-complete. Over one letter a solution is determined by the lengths $|\sigma(x)| \in \mathbb{N}$, so the equations become linear Diophantine equations with unary coefficients. This establishes the main unary-system hardness claim with its nonempty-side convention.

**Derived consequence, not stated in this precise form by the cited sources.** Satisfiability of a single equation over the fixed alphabet $\{a,b\}$ with both input sides nonempty is NP-hard, still allowing erasing solutions. The following direct derivation also gives an alternative proof of the main unary theorem.

Given an EXACT COVER BY 3-SETS instance with a number $q$ and a list of candidate sets $C_1, \dots, C_r$, output the unsatisfiable equation $a = aa$ if the instance is not well formed or if $r < q$, since then no $q$ disjoint triples exist; output the empty system if $q = 0$. Otherwise $3q \le 3r$, so the universe $\{0, \dots, 3q - 1\}$ can be listed in polynomial time: take one variable $x_j$ per candidate set and, for every element $e$, the equation $x_{j_1} x_{j_2} \cdots x_{j_t} = a$, where $C_{j_1}, \dots, C_{j_t}$ are the candidate sets containing $e$, or $a = aa$ if there are none. Every solution, over $\{a\}$ or over $\{a,b\}$, gives each variable the value $\varepsilon$ or $a$, since its value is a factor of $a$ (every variable occurs, as a well-formed candidate set has three elements), and gives exactly one set containing each element the value $a$; hence solutions correspond to exact covers.

The same system read over $\{a,b\}$ has the same solutions. Apply the [polynomial reduction from systems over at least two letters to one equation](system-of-word-equations-to-one-equation.md), mapping the empty system to $a=a$. Its construction produces two nonempty sides when the input system is nonempty and all its sides are nonempty. Composing these reductions yields the derived binary single-equation claim. Both unary-system and binary single-equation hardness also hold if empty input sides are allowed, by inclusion of the restricted instances. These latter consequences are derived here, rather than attributed to a source statement.

## Sources

- Volker Diekert, "Makanin's Algorithm for Solving Word Equations with Regular Constraints", Report Nr. 1998/02, Fakultät Informatik, Universität Stuttgart (1998), https://elib.uni-stuttgart.de/server/api/core/bitstreams/3846bd76-7ca9-4e0d-8595-75cc76db3018/content; with minor modifications Chapter 12, "Makanin's Algorithm", of M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge University Press (2002), 387–442, https://doi.org/10.1017/CBO9781107326019.013, Section 6 (Notes), stating NP-hardness as the known lower bound for equations without regular constraints, and Problems 1.2 and 2.3 (NP-hardness for systems via linear integer programming in unary notation with one constant, and for single equations)
- Aleksi Saarela, "Hardness Results for Constant-Free Pattern Languages and Word Equations", ICALP 2020, LIPIcs 168, Article 140 (2020), https://doi.org/10.4230/LIPIcs.ICALP.2020.140, Section 2, pp. 140:4–6 (nonempty patterns, erasing solutions, the unary-system problem $\mathrm{EqSat}(?,1)$ and its equivalence to NP-complete unary integer programming; followed by the separate system-to-one-equation result over at least two constants); Section 1 for general satisfiability bounds
- Volker Diekert, "More Than 1700 Years of Word Equations", Algebraic Informatics (CAI 2015), LNCS 9270, 22–28 (2015), https://doi.org/10.1007/978-3-319-23021-4_2; read as arXiv:1507.03215v1, https://arxiv.org/abs/1507.03215v1, Section "History"
