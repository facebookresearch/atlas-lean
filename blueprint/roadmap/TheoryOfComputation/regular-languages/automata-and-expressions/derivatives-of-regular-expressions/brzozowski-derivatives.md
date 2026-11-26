# Brzozowski derivatives of regular expressions

Regular expressions over an alphabet $\Sigma$ are built from $0$ (empty language), $1$ (empty word), letters $a$, sum $r + s$, concatenation $r \cdot s$
and star $r^*$, with their usual [languages](../kleene-s-theorem/is-regex-denoted.md) $L(r)$. Let $\mathrm{nullable}(r)$ hold when the empty word is in $L(r)$, computed by
structural recursion. The *derivative* of $r$ with respect to a letter $a$ is defined by
$$\partial_a 0 = \partial_a 1 = 0,\quad \partial_a b = (1 \text{ if } b = a \text{ else } 0),\quad \partial_a (r + s) = \partial_a r + \partial_a s,\quad \partial_a r^* = \partial_a r \cdot r^*,$$
$$\partial_a (r \cdot s) = \begin{cases} \partial_a r \cdot s + \partial_a s & \text{if } \mathrm{nullable}(r),\\ \partial_a r \cdot s & \text{otherwise,}\end{cases}$$
and extended to words by $\partial_\varepsilon r = r$ and $\partial_{wa} r = \partial_a(\partial_w r)$. By induction on $r$, $L(\partial_a r) = a^{-1} L(r) = \{w : aw \in L(r)\}$, so $w \in L(r)$ if
and only if $\partial_w r$ is nullable (Brzozowski).

## Depends on

- [Language denoted by a regular expression](../kleene-s-theorem/is-regex-denoted.md)

## Sources

- T. Nipkow and D. Traytel, "Unified decision procedures for regular expression equivalence", *Interactive Theorem Proving (ITP 2014)*, Lecture Notes in Computer Science 8558, Springer, 2014, author copy <https://www21.in.tum.de/~nipkow/pubs/regex_equiv.pdf>: Section 4.1, the definition of $\mathrm{der}$ and the characteristic property $L(\mathrm{der}\,a\,r) = D_a(L\,r)$, crediting J. A. Brzozowski, "Derivatives of regular expressions", *Journal of the ACM* 11 (1964).
