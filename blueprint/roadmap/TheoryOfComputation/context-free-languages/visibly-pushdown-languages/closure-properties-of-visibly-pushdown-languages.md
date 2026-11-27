# Closure properties of visibly pushdown languages

Let $L_1$ and $L_2$ be [visibly pushdown languages](visibly-pushdown-automata.md) with respect to the same pushdown alphabet $\tilde\Sigma$. Then $L_1 \cup L_2$,
$L_1 \cap L_2$, the concatenation $L_1 L_2$, the Kleene star $L_1^*$ and the complement $\Sigma^* \setminus L_1$ are visibly pushdown languages with respect to $\tilde\Sigma$, and
so is $f(L_1)$ for every renaming $f$ that maps calls to calls, returns to returns and local actions to local actions. Intersection is
the product construction, which is possible because both automata push and pop on the same letters; complement uses
[determinization](determinization-of-visibly-pushdown-automata.md). Context-free languages, by contrast, are not closed under intersection
or complement.

## Depends on

- [Visibly pushdown automata and visibly pushdown languages](visibly-pushdown-automata.md)

## Proof depends on

- [Determinization of visibly pushdown automata](determinization-of-visibly-pushdown-automata.md)

## Sources

- R. Alur and P. Madhusudan, "Visibly pushdown languages", *Proceedings of the 36th ACM STOC*, 2004; full version of August 2005, whose numbering is cited, <https://www.cis.upenn.edu/~alur/Stoc04.pdf>: Section 2.2, Theorem 1 (closure) with its proof and Corollary 1 (closure under complementation).
