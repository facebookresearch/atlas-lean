# Antimirov partial derivatives

The *partial derivative* of a regular expression $r$ with respect to a letter $a$ is the finite set of regular expressions defined by

$$\mathrm{pder}_a 0 = \mathrm{pder}_a 1 = \emptyset,\quad \mathrm{pder}_a b = (\{1\} \text{ if } b = a \text{ else } \emptyset),\quad \mathrm{pder}_a(r + s) = \mathrm{pder}_a r \cup \mathrm{pder}_a s,$$

$$\mathrm{pder}_a(r \cdot s) = \begin{cases} \mathrm{pder}_a r \odot s \cup \mathrm{pder}_a s & \text{if } \mathrm{matchEpsilon}(r),\\ \mathrm{pder}_a r \odot s & \text{otherwise,}\end{cases}\qquad \mathrm{pder}_a(r^*) = \mathrm{pder}_a r \odot r^*,$$

where $R \odot s = \{t \cdot s : t \in R\}$ and $\mathrm{matchEpsilon}(r)$, as for [Brzozowski derivatives](brzozowski-derivatives.md), holds when the empty word belongs to $L(r)$ (Antimirov). By induction on $r$, $a^{-1} L(r) = \bigcup_{s \in \mathrm{pder}_a r} L(s)$, the analogue for sets of the property of
[Brzozowski derivatives](brzozowski-derivatives.md). Starting from $\{r\}$ and applying $\mathrm{pder}_a$ elementwise reaches only finitely many sets, which gives a
nondeterministic automaton whose states are regular expressions, or after the subset construction a deterministic one, recognizing $L(r)$.

## Depends on

- [Brzozowski derivatives of regular expressions](brzozowski-derivatives.md)

## Sources

- T. Nipkow and D. Traytel, "Unified decision procedures for regular expression equivalence", *Interactive Theorem Proving (ITP 2014)*, Lecture Notes in Computer Science 8558, Springer, 2014, author copy <https://www21.in.tum.de/~nipkow/pubs/regex_equiv.pdf>: Section 4.2, the definition of $\mathrm{pder}$, the characteristic property and the interpretation $P$ with its finiteness, crediting V. Antimirov, "Partial derivatives of regular expressions and finite automaton constructions", *Theoretical Computer Science* 155 (1996).
