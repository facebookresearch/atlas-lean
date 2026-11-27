# Brzozowski derivatives of regular expressions

Regular expressions over an alphabet $\alpha$ with decidable equality are built from $0$ (empty language), $1$ (empty word), letters, sum $P + Q$,
concatenation $P \cdot Q$ and star $P^*$. Let $\mathrm{matchEpsilon}(P)$ be the Boolean that holds when $P$ matches the empty word, computed by structural
recursion: false for $0$ and letters, true for $1$ and $P^*$, the disjunction for $P + Q$ and the conjunction for $P \cdot Q$. The *Brzozowski derivative*
of $P$ with respect to a letter $a$ is defined by
$\partial_a 0 = \partial_a 1 = 0$, $\partial_a b = 1$ if $b = a$ and $0$ otherwise, $\partial_a (P + Q) = \partial_a P + \partial_a Q$, $\partial_a P^* = \partial_a P \cdot P^*$, and
$\partial_a (P \cdot Q) = \partial_a P \cdot Q + \partial_a Q$ if $\mathrm{matchEpsilon}(P)$ and $\partial_a P \cdot Q$ otherwise. The derivative of $P$ matches a word $x$
exactly when $P$ matches $a x$.

## Sources

- T. Nipkow and D. Traytel, "Unified decision procedures for regular expression equivalence", *Interactive Theorem Proving (ITP 2014)*, Lecture Notes in Computer Science 8558, Springer, 2014, author copy <https://www21.in.tum.de/~nipkow/pubs/regex_equiv.pdf>: Section 4.1, the definition of $\mathrm{der}$ and the characteristic property $L(\mathrm{der}\,a\,r) = D_a(L\,r)$, crediting J. A. Brzozowski, "Derivatives of regular expressions", *Journal of the ACM* 11 (1964).
