# Elimination Theorem

Let $k$ be a field and index the variables by a linearly ordered set $\sigma$ in which every
nonempty subset has a largest element, for instance $\sigma = \{0, \dots, n\}$; this makes the
lexicographic order in which $x_i > x_j$ for $i < j$, as in $x_0 > x_1 > \cdots > x_n$, a monomial
order. Let $G$ be a Gröbner basis of an ideal $I \subseteq k[x_i : i \in \sigma]$ for this order,
let $S \subseteq \sigma$ be a final segment, such as $\{l, l + 1, \dots, n\}$, and let $k[S]$ be the
subring of polynomials in the variables $x_i$ with $i \in S$. Then the leading monomial of every
nonzero polynomial of the elimination ideal $I \cap k[S]$ is divisible by the leading monomial of a
nonzero element of $G \cap k[S]$: the elements of $G$ that involve only the variables in $S$ form a
Gröbner basis of $I \cap k[S]$, in the leading-monomial sense of the definition.

The proof rests on one property of the lexicographic order: a monomial that is lexicographically
below a monomial in the variables of $S$ is itself a monomial in the variables of $S$ (Hassett:
lexicographic order is an elimination order). So once the leading monomial of $g \in G$ divides that
of some $f \in k[S]$, all of $g$ lies in $k[S]$.

Computing one lexicographic Gröbner basis thus produces generators for all the elimination ideals at
once, which is how Gröbner bases project varieties, implicitize parametrizations and bring
polynomial systems to triangular form. That these elements generate $I \cap k[S]$ inside $k[S]$, as
Hassett states it, follows by the division argument of [A Gröbner basis generates its
ideal](span-eq.md), carried out in $k[S]$.

## Sources

- B. Hassett, *Math 465 Lecture Notes*, Brown University, 2002, Lecture 9, Definition 9.12, Example 9.13 and Theorem 9.14 (https://www.math.brown.edu/bhassett/teaching/465spring02/).
- D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Ch. 3 §1 (section only).
