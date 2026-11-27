# Satisfiability of word equations is NP-hard


Deciding whether a word equation with constants has a solution is NP-hard, already for systems over a one-letter alphabet and for single equations over a two-letter alphabet.

Each of the following decision problems on bitstrings is NP-hard, that is, every decision problem in NP has a polynomial-time many-one reduction to it; instances are encoded in the canonical way, with letters and variables written in binary.

1. Given a finite system of word equations over the one-letter alphabet $\{a\}$, decide whether it has a solution $\sigma : \mathcal{X} \to a^*$.
2. Given a single word equation over the two-letter alphabet $\{a, b\}$, decide whether it has a solution $\sigma : \mathcal{X} \to \{a, b\}^*$.

Solutions may be erasing. NP-hardness is the best known lower bound for WordEquations, and membership in NP is open; the best known upper bound is [PSPACE](word-equation-satisfiability-in-pspace.md).


## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [EXACT COVER BY 3-SETS is NP-complete](../../../np-completeness/set-systems-and-location/exact-cover-by-3-sets/exact-cover-by3-sets-np-complete.md)
- [NP-hardness transfers along reductions](../../../np-completeness/satisfiability/3-satisfiability/np-hard-of-poly-many-one-red.md)
- [Systems of word equations reduce to one equation](system-of-word-equations-to-one-equation.md)

## Expansion

The sources prove item 1 by observing that over a one-letter alphabet a solution is determined by the lengths $|\sigma(x)| \in \mathbb{N}$, so a system of unary word equations is a system of linear Diophantine equations over $\mathbb{N}$ with coefficients written in unary, and linear integer programming in this form is NP-hard; item 2 follows by the reduction of systems to one equation over two letters. Saarela states the unary problem in his convention that both sides of an equation are nonempty.

The proof given here is a direct alternative, not printed in the cited sources, which reduces from EXACT COVER BY 3-SETS and produces only equations with nonempty sides. Given an instance with a number $q$ and a list of candidate sets $C_1, \dots, C_r$, output the unsatisfiable equation $a = aa$ if the instance is not well formed or if $r < q$, since then no $q$ disjoint triples exist; output the empty system if $q = 0$. Otherwise $3q \le 3r$, so the universe $\{0, \dots, 3q - 1\}$ can be listed in polynomial time: take one variable $x_j$ per candidate set and, for every element $e$, the equation $x_{j_1} x_{j_2} \cdots x_{j_t} = a$, where $C_{j_1}, \dots, C_{j_t}$ are the candidate sets containing $e$, or $a = aa$ if there are none. Every solution, over $\{a\}$ or over $\{a, b\}$, gives each variable the value $\varepsilon$ or $a$, since its value is a factor of $a$ (every variable occurs, as a well-formed candidate set has three elements), and gives exactly one set containing each element the value $a$; hence solutions correspond to exact covers. The same system read over $\{a, b\}$ has the same solutions, and the reduction to one equation over $\{a, b\}$ yields item 2, with the empty system mapped to $a = a$. Composing with the NP-hardness of EXACT COVER BY 3-SETS gives both items.

## Sources

- Volker Diekert, "Makanin's Algorithm for Solving Word Equations with Regular Constraints", Report Nr. 1998/02, Fakultät Informatik, Universität Stuttgart (1998), https://elib.uni-stuttgart.de/server/api/core/bitstreams/3846bd76-7ca9-4e0d-8595-75cc76db3018/content; with minor modifications Chapter 12, "Makanin's Algorithm", of M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge University Press (2002), 387–442, https://doi.org/10.1017/CBO9781107326019.013, Section 6 (Notes), stating NP-hardness as the known lower bound for equations without regular constraints, and Problems 1.2 and 2.3 (NP-hardness for systems via linear integer programming in unary notation with one constant, and for single equations)
- Aleksi Saarela, "Hardness Results for Constant-Free Pattern Languages and Word Equations", ICALP 2020, LIPIcs 168, Article 140 (2020), https://doi.org/10.4230/LIPIcs.ICALP.2020.140, Section 1 (NP-hardness via linear integer programming and pattern membership; NP-completeness open) and Section 2 (the unary problem is equivalent to linear integer programming in unary notation, which is NP-complete)
- Volker Diekert, "More Than 1700 Years of Word Equations", Algebraic Informatics (CAI 2015), LNCS 9270, 22–28 (2015), https://doi.org/10.1007/978-3-319-23021-4_2; read as arXiv:1507.03215v1, https://arxiv.org/abs/1507.03215v1, Section "History"
