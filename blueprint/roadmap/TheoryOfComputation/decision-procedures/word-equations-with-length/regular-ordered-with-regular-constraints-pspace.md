# Regular-ordered equations with regular constraints are PSPACE-complete

With regular constraints given by explicit nondeterministic finite automata, satisfiability is PSPACE-complete already for regular-ordered word equations, and remains in PSPACE for all quadratic equations.

Let the input be a word equation $\alpha = \beta$ over an alphabet of constants $A$ together with, for each variable $x$ of the equation, a regular constraint $L_x \subseteq A^*$ given by an explicitly listed nondeterministic finite automaton; the question is whether some solution $h$ (variables mapped to possibly empty words) satisfies $h(x) \in L_x$ for every $x$. The size of the input is the length of its encoding, including all states and transitions of the automata.

1. For quadratic equations, and so for regular-ordered ones, the problem is in PSPACE.
2. The problem is PSPACE-hard already for regular-ordered equations of the form $x_1 \# x_2 \# \cdots \# x_{m-1} = x_2 \# x_3 \# \cdots \# x_m$ with one constant $\#$ not in the alphabets of the automata.

Hence satisfiability of regular-ordered (and of quadratic, and of regular) word equations with explicit NFA constraints is PSPACE-complete.

## Depends on

- [Word equations with length and regular constraints](length-and-regular-constraints.md)
- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)
- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Nielsen transformations decide quadratic word equations](nielsen-transformations-solve-quadratic-equations.md)

## Expansion

(1) is the third statement of the page on Nielsen transformations for quadratic equations. (General word equations with explicit NFA constraints are also in PSPACE, by the extension of Plandowski's method to regular constraints, but that is not needed here.)

(2) reduces the *intersection nonemptiness* problem for nondeterministic finite automata, deciding whether $\bigcap_{i=1}^m L(M_i) \ne \varnothing$ for given NFAs $M_1, \dots, M_m$ over $\Sigma$, which is PSPACE-hard (Kozen). With $\# \notin \Sigma$, take $\alpha = x_1 \# x_2 \# \cdots \# x_{m-1}$, $\beta = x_2 \# x_3 \# \cdots \# x_m$ and constraints $L_{x_i} = L(M_i)$. If $w$ lies in the intersection, then $h(x_i) = w$ for all $i$ is a solution. Conversely, in a solution no $h(x_i)$ contains $\#$, so comparing the $\#$-separated blocks gives $h(x_1) = h(x_2) = \cdots = h(x_m)$, a word in every $L(M_i)$. Each variable occurs at most once per side, and the shared variables $x_2, \dots, x_{m-1}$ occur in the same order on both sides, so the equation is regular-ordered; it is not strictly regular-ordered, since $x_1$ and $x_m$ occur on one side only. The PSPACE-hardness of intersection nonemptiness is a classical result without a page here.

## Sources

- Florin Manea, Dirk Nowotka and Markus L. Schmid, "On the Solvability Problem for Restricted Classes of Word Equations", Developments in Language Theory (DLT 2016), LNCS 9840, pp. 306–318, 2016, <https://doi.org/10.1007/978-3-662-53132-7_25>; read as the author preprint <http://www.mlschmid.de/preprints/conferences/2016_DLT_preprint.pdf>, Theorem 7 (PSPACE-completeness for regular equations, with the reduction above from the PSPACE-hard intersection emptiness problem for NFAs) and Section 2 (regular constraints given as NFAs).
- Joel D. Day, Florin Manea and Dirk Nowotka, "The Hardness of Solving Simple Word Equations", 42nd International Symposium on Mathematical Foundations of Computer Science (MFCS 2017), LIPIcs 83, Article 18, pp. 18:1–18:14, 2017, <https://doi.org/10.4230/LIPIcs.MFCS.2017.18>, Section 2 (regular constraints as NFAs) and Proposition 19 (PSPACE-completeness for regular-ordered equations).
- Anthony W. Lin and Rupak Majumdar, "Quadratic Word Equations with Length Constraints, Counter Systems, and Presburger Arithmetic with Divisibility", *Logical Methods in Computer Science* 17(4:4), 2021, <https://doi.org/10.46298/lmcs-17(4:4)2021>; read as the accepted version arXiv:2007.15478v6, Proposition 3.2 (PSPACE for quadratic equations with regular constraints).
