# Regular word equations are NP-complete

Deciding whether a regular word equation, one in which each variable occurs at most once on each side, has a solution is NP-complete. Membership in NP comes from short paths in the Nielsen graph, not from a bound on solution length.

Let the input be a regular word equation $E$ given by $\alpha = \beta$ over an alphabet of constants with at least two letters given with the input, of size $|E| = |\alpha\beta|$; solutions map variables to possibly empty words over the constants. The problem of deciding whether $E$ has a solution is NP-complete.

## Depends on

- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Nielsen transformations decide quadratic word equations](nielsen-transformations-solve-quadratic-equations.md)
- [Nielsen graphs of regular equations have polynomial diameter](nielsen-graphs-of-regular-equations-diameter.md)
- [Regular-ordered word equations are NP-complete](regular-ordered-equations-are-np-complete.md)

## Expansion

Hardness: regular-ordered equations are regular, and their satisfiability problem is NP-hard. The hard instances of that reduction use four constants; the statement here is the uniform one, with the alphabet part of the input, and no claim is made for every fixed alphabet of size at least two.

Membership (Proposition 3.4 of the source): $E$ has a solution if and only if $\varepsilon = \varepsilon$ is reachable from $E$ in its Nielsen graph. If it is reachable, it is reachable by a path of length at most the diameter of the graph, which is $O(|E|^{12})$. Every equation on the path has length at most $|E|$, so a nondeterministic algorithm guesses the path and verifies each step in linear time, in total time $O(|E|^{13})$. The certificate is a path, not a solution: minimal solutions of regular equations need not be short in any sense the argument uses, and the chain-square-free solutions used to bound minimal solutions of regular-ordered equations can be exponentially long for regular-reversed equations such as $x_n x_{n-1} \cdots x_1 a = a x_1 \cdots x_{n-1} x_n$, which has a chain-square-free solution of length $2^n$ that is not minimal.

The source also proves NP-completeness for systems of equations that are regular under its separate definition of regular systems (Theorem 11.2), by applying transformations rooted at one equation of the system at a time; this does not follow from the single-equation statement alone.

## Sources

- Joel D. Day and Florin Manea, "On the structure of solution-sets to regular word equations", *Theory of Computing Systems* 68:662–739, 2024, <https://doi.org/10.1007/s00224-021-10058-5>, Proposition 3.4 (polynomial diameter implies NP), Theorem 8.11 (diameter), Theorem 8.12 (NP-completeness), Section 11 with Theorem 11.2 (regular systems), Section 2 (alphabet with at least two letters). Conference version: Joel D. Day and Florín Manea, "On the Structure of Solution Sets to Regular Word Equations", ICALP 2020, LIPIcs 168, Article 124, <https://doi.org/10.4230/LIPIcs.ICALP.2020.124>.
- Joel D. Day, Florin Manea and Dirk Nowotka, "The Hardness of Solving Simple Word Equations", MFCS 2017, LIPIcs 83, Article 18, <https://doi.org/10.4230/LIPIcs.MFCS.2017.18>, Theorem 4 (NP-hardness for regular-ordered equations).
- Joel D. Day, Florin Manea and Dirk Nowotka, "Upper Bounds on the Length of Minimal Solutions to Certain Quadratic Word Equations", 44th International Symposium on Mathematical Foundations of Computer Science (MFCS 2019), LIPIcs 138, Article 44, pp. 44:1–44:15, 2019, <https://doi.org/10.4230/LIPIcs.MFCS.2019.44>, Proposition 14 (the equation $x_n \cdots x_1 a = a x_1 \cdots x_n$ with a chain-square-free, non-minimal solution of length $2^n$).
