# Value of a word under a recursion scheme in STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES

In STRONG INEQUIVALENCE FOR MONADIC RECURSION SCHEMES, fix a [recursion scheme](recursion-scheme.md) $S$, an interpretation $a_k \mapsto f_k : D \to D$ of the symbols of $F$ and $p_j \mapsto P_j : D \to \{T, F\}$ of the predicates. A word $w$ over $F \cup G$ applied to $x \in D$ has value $y$ under $S$ when this is derived by finitely many applications of the following rules; the relation is the **least** one closed under them, so a value is defined only when it has a finite derivation.

- The empty word applied to $x$ has value $x$.
- If $w$ applied to $x$ has value $y$, then $a_k w$ applied to $x$ has value $f_k(y)$.
- If $w$ applied to $x$ has value $y$, the $k$-th defining statement of $S$ (counting from $0$) exists and is $g_k x = \text{if } p_j x \text{ then } \alpha x \text{ else } \beta x$, and the word $\alpha$ (when $P_j(y) = T$) or $\beta$ (when $P_j(y) = F$) applied to $y$ has value $z$, then $g_k w$ applied to $x$ has value $z$.

A defined symbol $g_k$ for which $S$ has no $k$-th statement has no value. A statement with no base case, such as $g_0 x = \text{if } p_0 x \text{ then } g_0 x \text{ else } g_0 x$, gives $g_0$ no value at any $x$.
