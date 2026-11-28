# Negation reduces length constraints to one-terminal equations

With negated equations allowed, a single constant letter suffices to express any word equation with linear length constraints, over a target alphabet with at least two letters. So one-terminal formulas with negation and length constraints are at least as hard as the open general problem.

Let $A$ be a finite alphabet of constants with $|A| \ge 2$ and $a \in A$. For every word equation $U = V$ with $U, V \in (A \cup X)^*$ and every set $\theta$ of linear length constraints (a system of linear equations in the lengths $|x|$), one can construct a set $X' \supseteq X$ of variables, a finite conjunction $\mathcal S$ of equations $U_i = V_i$ and negated equations $U_i \neq V_i$ with $U_i, V_i \in (X' \cup \{a\})^*$, and a set $\theta' \supseteq \theta$ of linear length constraints, such that $\mathcal S$ together with $\theta'$ has a solution in $A^*$ if and only if $U = V$ together with $\theta$ has a solution in $A^*$.

## Depends on

- [Word equations with length and regular constraints](length-and-regular-constraints.md)
- [Solution of a word equation](../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

None.

## Expansion

Write $A = \{a_1, \dots, a_n\}$ with $a_1 = a$ and introduce fresh variables $y_1, \dots, y_n$. Let $U' = V'$ be obtained from $U = V$ by replacing each letter $a_i$ by $y_i$, and let $\mathcal S$ consist of $U' = V'$, the equation $y_1 = a$ and the inequations $y_i \neq y_j$ for $i < j$, with $\theta' = \theta$ together with $|y_i| = 1$ for $2 \le i \le n$. The only constant occurring is $a$. In any solution, $y_1 = a$ and the $y_i$ are pairwise distinct single letters, so $i \mapsto y_i$ is a permutation $\pi$ of $A$ fixing $a$. If $h'$ solves $\mathcal S$ and $\theta'$, then applying $\pi^{-1}$ letterwise to the values of the original variables gives a solution of $U = V$ with the same lengths, so $\theta$ still holds. Conversely, a solution of $U = V$ and $\theta$ extends by $y_i = a_i$. *Size (analysis of the construction, not stated in the sources):* with the alphabet $A$ listed explicitly as part of the input, the construction adds $n$ variables, $n - 1$ length equations and $n(n-1)/2$ inequations, so it is computable in time polynomial in the size of the input.

The source also states the reverse comparison: there is a reduction from quantifier-free formulas over one-terminal equations with length constraints to word equations with length constraints. This needs a conversion of Boolean combinations of word equations into a single equation that keeps the values, and hence the lengths, of the original variables, as in the construction of Karhumäki, Mignosi and Plandowski restated by Day et al. (ToCS 2024, Lemma 3). That direction is not part of the statement above. Over a one-letter alphabet ($|A| = 1$) the whole quantifier-free theory with length constraints is a fragment of Presburger arithmetic and is decidable. Without negation the one-terminal problem is NP-complete.

## Sources

- Joel D. Day, Vijay Ganesh, Paul He, Florin Manea and Dirk Nowotka, "The Satisfiability of Word Equations: Decidable and Undecidable Theories", Reachability Problems (RP 2018), LNCS 11123, pp. 15–29, 2018, <https://doi.org/10.1007/978-3-030-00250-3_2>, Theorem 3 and the preceding paragraph (equivalence with the general problem, one direction immediate), Section 3.2 (the unary case as Presburger arithmetic).
- Joel Day, Vijay Ganesh, Paul He, Florin Manea and Dirk Nowotka, "The Satisfiability of Extended Word Equations: The Boundary Between Decidability and Undecidability", arXiv:1802.00523v1, 2018 (extended version), Theorem 5.2 and its proof (the permutation construction) and the remark after it on $|A| = 1$.
- Joel D. Day, Vijay Ganesh, Nathan Grewal, Matthew Konefal and Florin Manea, "A Closer Look at the Expressive Power of Logics Based on Word Equations", *Theory of Computing Systems* 68:322–379, 2024, <https://doi.org/10.1007/s00224-023-10154-8>, Lemma 3 (Boolean combinations of word equations as one equation, preserving the values of the original variables).
