# Nonperiodic satisfiability of constant-free word equations is NP-hard

Deciding whether a system of constant-free word equations has a solution in which not all variables commute is NP-hard, already for solutions over a binary alphabet.

Let $\Sigma_2 = \{0, 1\}$. The nonperiodic satisfiability problem of constant-free word equations asks: given a finite alphabet $\Xi$ of variables and a finite system $S$ of equations $(U, V)$ with nonempty sides $U, V \in \Xi^+$, is there a morphism $\alpha : \Xi^* \to \Sigma_2^*$, possibly erasing, with $\alpha(U) = \alpha(V)$ for every equation of $S$ and $\alpha(xy) \neq \alpha(yx)$ for some $x, y \in \Xi$? This problem is NP-hard: every decision problem in NP has a polynomial-time many-one reduction to it. More precisely, for every $n \ge 1$, satisfiability of systems of word equations with nonempty sides and $n$ variables over the one-letter alphabet $\{0\}$ reduces in polynomial time to it with $n + 2$ variables.

Constant-free equations always have periodic solutions, such as the morphism sending every variable to the empty word, so asking for a nonperiodic solution is the natural nontrivial question.

## Depends on

- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Satisfiability of unary word-equation systems is NP-hard](../satisfiability/word-equation-satisfiability-is-np-hard.md)
- [NP-hardness transfers along reductions](../../../np-completeness/satisfiability/3-satisfiability/np-hard-of-poly-many-one-red.md)
- [Commuting words are powers of a common word](../../word-equations-with-length/commuting-words-are-powers-of-a-common-word.md)
- [Unique primitive root of a word](unique-primitive-root.md)
- [Nonperiodic morphisms preserve primitivity of binary words](primitive-images-of-binary-primitive-words.md)

## Expansion

Let $S$ be a system over variables $\Xi$ and the single constant $0$. Introduce two new variables $a, b$, replace each occurrence of $0$ by $a^2 b^2$, and add the equations $x\, a^2 b^2 = a^2 b^2\, x$ and $xy = yx$ for all $x, y \in \Xi$. A solution $\alpha$ of $S$ gives the nonperiodic solution $a \mapsto 0$, $b \mapsto 1$, $x \mapsto \tau(\sigma(\alpha(x)))$, where $\sigma(0) = a^2 b^2$ and $\tau$ renames $a, b$ to $0, 1$. Conversely, let $\beta$ be a nonperiodic solution. The added equations make the words $\beta(x)$ for $x \in \Xi$ and $\beta(a^2 b^2)$ commute pairwise. If they are all empty, then $\beta(a) = \beta(b) = \varepsilon$ and $\beta$ is periodic; otherwise they all lie in $R^*$ for one primitive word $R$. If $\beta(ab) = \beta(ba)$, then $\beta(a)$ and $\beta(b)$ are powers of a common word, and $\beta(a^2 b^2)$, if nonempty, has the same primitive root as that word, so $\beta(a), \beta(b) \in R^*$ and $\beta$ would be periodic; if $\beta(a^2 b^2)$ is empty, then $\beta(a) = \beta(b) = \varepsilon$, again periodic; so $\beta(ab) \neq \beta(ba)$, and since $a^2 b^2$ is primitive with two occurrences of each letter, $\beta(a^2 b^2)$ is primitive, hence equals $R$. Identifying $R$ with $0$ turns $\beta$ into a solution of $S$. NP-hardness of the unary problem completes the reduction; if necessary, add a fresh variable $z$ and the tautological equation $z=z$ first to meet $n \ge 1$.

## Sources

- Aleksi Saarela, "Hardness Results for Constant-Free Pattern Languages and Word Equations", ICALP 2020, LIPIcs 168, Article 140 (2020), https://doi.org/10.4230/LIPIcs.ICALP.2020.140, Theorem 13 and Corollary 14 (Section 4, "Nonperiodic satisfiability"), with Theorems 1 and 7 (Section 2)
