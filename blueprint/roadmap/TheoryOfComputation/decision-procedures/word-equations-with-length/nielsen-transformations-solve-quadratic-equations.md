# Nielsen transformations decide quadratic word equations

A quadratic word equation has a solution exactly when the trivial equation is reachable from it by Nielsen transformations. Because the reachable equations are finitely many and no longer than the input, satisfiability of quadratic word equations is in PSPACE, also with explicit NFA regular constraints.

Let $A$ be a finite alphabet of constants, let $E$ be a quadratic word equation $\alpha = \beta$ over $A$ and a set of variables, and let $\Rightarrow_{NT}$ be the Nielsen transformation relation of Day and Manea. Solutions map variables to words in $A^*$, the empty word allowed.

1. $E$ has a solution if and only if $E \Rightarrow_{NT}^* (\varepsilon = \varepsilon)$.
2. The problem of deciding whether a given quadratic word equation has a solution is in PSPACE.
3. The problem of deciding whether a given quadratic word equation with regular constraints, each given by an explicitly listed nondeterministic finite automaton, has a solution satisfying all constraints is in PSPACE.

Only membership in PSPACE is claimed; quadratic equations without constraints are NP-hard, and their exact complexity is not settled here.

## Depends on

- [Nielsen transformations of quadratic word equations](nielsen-transformations.md)
- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)
- [Word equations with length and regular constraints](length-and-regular-constraints.md)
- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Length-directed Levi's lemma](../string-constraints-and-word-equations/levi-of-le.md)
- [Savitch's theorem: NPSPACE = PSPACE](../../complexity-classes/savitch.md)

## Expansion

(1) Soundness: each step comes with an inverse transformation of assignments. If $E \Rightarrow_L E'$ substitutes $yz$ for $z$ and $h'$ solves $E'$, then $h$ with $h(z) = h'(y)h'(z)$ and $h = h'$ elsewhere solves $E$; a step $\Rightarrow_>$ that erases a set $Y$ is inverted by mapping $Y$ to the empty word, and cancelling a common leading symbol or absorbing a symbol into a once-occurring variable is inverted similarly. Hence reaching $\varepsilon = \varepsilon$, which is solved by every assignment, yields a solution of $E$. Completeness: let $h$ solve $E = (z\alpha' = y\beta')$. If some variable has an empty image, erase it. Otherwise the leading images $h(z)$ and $h(y)$ are both nonempty prefixes of the same word, so by the length-directed Levi lemma one is a prefix of the other, $h(z) = h(y)w$ say. If $z = y$, cancel; if $z$ occurs once, absorb $y$ into it; otherwise apply $\Rightarrow_L$ and keep the solution $h'$ with $h'(z) = w$. In each case either the equation gets shorter, or it keeps its length and the solution word $h'(\alpha')$ is strictly shorter than $h(\alpha)$, because $h(y)$ is nonempty and has been cancelled. Equations reachable from $E$ are finitely many, so this progress measure (equation length, then solution length) cannot decrease forever, and $\varepsilon = \varepsilon$ is reached.

(2) Every equation reachable from $E$ is quadratic, uses only symbols of $E$ and has length at most $|E|$, and one step can be checked in polynomial time. A nondeterministic machine guesses a path from $E$ to $\varepsilon = \varepsilon$ step by step, storing only the current equation and a step counter bounded by the number of equations of length at most $|E|$ over the symbols of $E$, which is exponential and thus has a polynomial-size counter. So the problem is in NPSPACE, which equals PSPACE by Savitch's theorem.

(3) Lin and Majumdar use their variant of the rules (Levi's method) annotated with transition matrices. Let the automata have $r$ states in total. For a word $w$, let $M_w$ be the Boolean $r \times r$ matrix whose $(p, q)$ entry records whether some automaton has a run from $p$ to $q$ on $w$; $w \mapsto M_w$ is a morphism into the finite monoid of Boolean matrices. A configuration is a pair $(E', f)$ where $f$ assigns a matrix to each variable. Initially one guesses $f$ that is consistent with the constraints (for $x \in L(\mathcal A)$, the entry from an initial to a final state of $\mathcal A$ in $f(x)$ is $1$) and realizable, meaning each $f(x)$ equals $M_w$ for some word $w$; realizability is checked by guessing $w$ letter by letter while storing only the current matrix. When a rule replaces $x$ by $yx$ or $ax$, the annotation is split into factors whose product is the old matrix, with the new value of $x$ again realizable; an erased variable must have the identity matrix, which is the matrix of the empty word. The trivial configuration is reached exactly when a solution satisfying the constraints exists. Configurations have polynomial size and the matrix monoid has at most $2^{r^2}$ elements, so a guessed accepting path can be bounded by an exponential cutoff and searched in nondeterministic polynomial space, hence PSPACE by Savitch's theorem.

## Sources

- Joel D. Day and Florin Manea, "On the structure of solution-sets to regular word equations", *Theory of Computing Systems* 68:662–739, 2024, <https://doi.org/10.1007/s00224-021-10058-5>, Theorem 3.3 (statement 1, attributed to M. Lothaire, *Algebraic Combinatorics on Words*, Chapter 12), Section 3 (the rules and the intuition for their correctness) and Remark 3.1 (finiteness and lengths).
- Anthony W. Lin and Rupak Majumdar, "Quadratic Word Equations with Length Constraints, Counter Systems, and Presburger Arithmetic with Divisibility", *Logical Methods in Computer Science* 17(4:4), 2021, <https://doi.org/10.46298/lmcs-17(4:4)2021>; numbering from the accepted version arXiv:2007.15478v6: Proposition 3.1 (iff and PSPACE for their variant, with the progress argument used above) and Section 3.2 with Proposition 3.2 (the matrix-annotated rules, consistency with the constraints, PSPACE via Savitch's theorem).
