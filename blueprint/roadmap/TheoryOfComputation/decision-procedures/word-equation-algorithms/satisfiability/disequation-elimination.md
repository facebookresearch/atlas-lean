# Elimination of a word disequation

A disequation $L \neq R$ between words with variables is equisatisfiable with a positive formula made of word equations in three new variables.

Let $A$ be a finite alphabet, let $L, R \in (A \cup \mathcal{X})^*$, and let $x, y, z$ be three pairwise distinct variables not in $\mathcal{X}$. Let $\Phi$ be the formula

$$
\bigvee_{a \in A} \big( L = R\,a\,x \;\lor\; R = L\,a\,x \big) \;\lor \bigvee_{\substack{a, b \in A \\ a \neq b}} \big( L = x\,a\,y \;\land\; R = x\,b\,z \big) .
$$

Then the disequation $L \neq R$ has a solution, a substitution $\sigma : \mathcal{X} \to A^*$ with $\sigma(L) \neq \sigma(R)$, if and only if $\Phi$ has a solution, a substitution of $\mathcal{X} \cup \{x, y, z\}$ making $\Phi$ true. Consequently every propositional combination of word equations and disequations is equisatisfiable with one without negations.

## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

None.

## Expansion

The proof shows more: a substitution $\sigma$ of $\mathcal{X}$ satisfies $\sigma(L) \neq \sigma(R)$ exactly when it extends to $x, y, z$ so that $\Phi$ holds. Two words $u \neq v$ over $A$ either are in the proper-prefix relation, $u = v a w$ or $v = u a w$ for a letter $a$ and a word $w$, which matches the first disjunction with $x = w$; or they have a longest common prefix $p$ followed by different letters, $u = p a w$ and $v = p b w'$ with $a \neq b$, which matches the second with $(x, y, z) = (p, w, w')$. Conversely each disjunct forces $\sigma(L) \neq \sigma(R)$, by comparing lengths in the first case and the letter after $x$ in the second. Over a one-letter alphabet the second disjunction is empty, and over the empty alphabet $\Phi$ is the empty disjunction, which is false, as $L \neq R$ then has no solution. Applying this to each negated equation, after pushing negations to the atoms and using fresh variables for each occurrence, removes all negations.

## Sources

- Volker Diekert, "Makanin's Algorithm for Solving Word Equations with Regular Constraints", Report Nr. 1998/02, Fakultät Informatik, Universität Stuttgart (1998), https://elib.uni-stuttgart.de/server/api/core/bitstreams/3846bd76-7ca9-4e0d-8595-75cc76db3018/content; with minor modifications Chapter 12, "Makanin's Algorithm", of M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge University Press (2002), 387–442, https://doi.org/10.1017/CBO9781107326019.013, Proposition 2.8 (Section 2.4), stated as equivalence with respect to satisfiability; the proof is left as Problem 2.2
