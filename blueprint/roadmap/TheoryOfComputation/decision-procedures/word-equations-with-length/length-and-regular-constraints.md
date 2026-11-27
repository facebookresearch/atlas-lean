# Word equations with length and regular constraints

A length constraint restricts the lengths of the words a solution assigns to the variables by linear arithmetic; a regular constraint requires the word assigned to a variable to lie in a given regular language. Adding either kind to a word equation defines a satisfiability problem.

Let $A$ be a nonempty finite alphabet of constants and $X$ a finite set of variables disjoint from $A$. A word equation $\alpha = \beta$ is a pair of words $\alpha, \beta \in (A \cup X)^*$, and a solution is a substitution $\sigma : X \to A^*$ (extended to $(A \cup X)^*$ as the morphism fixing every constant) with $\sigma(\alpha) = \sigma(\beta)$. Variables may be mapped to the empty word: solutions are taken in the free monoid $A^*$, not in the free semigroup $A^+$.

- A **length constraint** restricts the vector $(|\sigma(x)|)_{x \in X}$ of lengths. *Presburger arithmetic* is first-order logic over the structure $(\mathbb N, 0, 1, +, \le)$. Three presentations occur in the sources: (i) a Presburger formula whose free variables are among the length variables $|x|$, $x \in X$; (ii) a finite system of linear equations $c_0 + \sum_{x} c_x |x| = 0$ with integer coefficients; (iii) a quantifier-free Boolean combination of such linear equations. In every case $\sigma$ satisfies the constraint when it holds with $|x|$ interpreted as $|\sigma(x)|$, and integer coefficients are written in binary.
- A **regular constraint** for a variable $x$ is a regular language $L_x \subseteq A^*$, given by an explicitly listed nondeterministic finite automaton (states, initial and final states, and transitions labelled by letters), or by a deterministic one where a result says so. A solution $\sigma$ satisfies it when $\sigma(x) \in L_x$.

The **satisfiability problem for word equations with length constraints** asks, given $\alpha = \beta$ and a length constraint, whether some solution satisfies it; with regular constraints, whether some solution satisfies every $L_x$; with both, whether some solution satisfies all of them. In complexity statements the size of an instance is the length of its full encoding: the equation (letters and variables written as identifiers), the complete syntax of the length constraint including its coefficients in binary (and, for a Presburger formula, its connectives and quantifiers), the alphabet, and the full lists of states and transitions of the automata.

Whether the satisfiability problem for word equations with linear length constraints is decidable is an open problem. Decidability is known only for restricted classes of equations or constraints, and undecidability is known for stronger counting constraints.

## Depends on

- [Ordinary word equation](../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)
- [Encoded NFA](../encoded-finite-automata/encoded-nfa.md)

## Proof depends on

None.

## Expansion

This is a definition. The three presentations of length constraints are different input languages, and the sources treat them separately; no translation between them that preserves size is claimed here, so complexity statements always name the presentation they use. A system of linear equations is a special Boolean combination. In a positive, existential setting a strict inequality $c_0 + \sum c_x |x| < 0$ can be added with fresh string variables $y, z$ as $|y| = 1 \wedge c_0 + |y| + |z| + \sum c_x |x| = 0$, since $A$ is nonempty (Day et al., Remark 2); this is an existential projection, not a substitution that may be used under negation. Matiyasevich proposed word equations with length constraints as a route to the undecidability of Hilbert's tenth problem; Makanin's decidability theorem for word equations closed this route without length constraints, and the problem with length constraints remains open. Word equations with explicit NFA regular constraints alone remain decidable, and their satisfiability problem is PSPACE-complete.

## Sources

- Anthony W. Lin and Rupak Majumdar, "Quadratic Word Equations with Length Constraints, Counter Systems, and Presburger Arithmetic with Divisibility", *Logical Methods in Computer Science* 17(4:4), 2021, <https://doi.org/10.46298/lmcs-17(4:4)2021>; read as the accepted version arXiv:2007.15478v6, Section 2 (length constraints as Presburger formulas, regular constraints, the satisfiability problem) and Section 1 (open status).
- Joel D. Day, Vijay Ganesh, Nathan Grewal, Matthew Konefal and Florin Manea, "A Closer Look at the Expressive Power of Logics Based on Word Equations", *Theory of Computing Systems* 68:322–379, 2024, <https://doi.org/10.1007/s00224-023-10154-8>, Definitions 2–4 and Remark 2 (length atoms as linear equalities in a quantifier-free Boolean logic; simulation of strict inequalities by fresh variables), and Section 1 (open status).
- Joel D. Day, Vijay Ganesh, Paul He, Florin Manea and Dirk Nowotka, "The Satisfiability of Word Equations: Decidable and Undecidable Theories", Reachability Problems (RP 2018), LNCS 11123, pp. 15–29, 2018, <https://doi.org/10.1007/978-3-030-00250-3_2>, Section 2 (linear length constraints as systems of linear Diophantine equations, regular constraints by finite automata) and Section 1 (open status, Matiyasevich's reduction).
- Joel D. Day and Florin Manea, "On the structure of solution-sets to regular word equations", *Theory of Computing Systems* 68:662–739, 2024 (online 2021), <https://doi.org/10.1007/s00224-021-10058-5>, Section 1 (PSPACE-completeness with regular constraints, open status with length constraints).
- Laura Ciobanu, "Word Equations, Constraints, and Formal Languages", Developments in Language Theory (DLT 2024), LNCS 14791, 2024, <https://doi.org/10.1007/978-3-031-66159-4_1>; read as arXiv:2406.02160v1, Section 2 (problems (WordEqn, LEN) and (WordEqn, RAT)).
