# Exponent of periodicity

The exponent of periodicity of a word is the largest $k$ such that some nonempty word occurs in it as a factor $u^k$, and $0$ for the empty word; for a word equation with a nonerasing solution it is the largest value over its length-minimal solution words.

Let $A$ be a finite alphabet. For a word $w \in A^*$ the exponent of periodicity is

$$
\mathrm{per}(w) = \max \big( \{0\} \cup \{ k \ge 1 : u^k \text{ is a factor of } w \text{ for some } u \in A^+ \} \big) ,
$$

so $\mathrm{per}(\varepsilon) = 0$ and $\mathrm{per}(w) \ge 1$ for nonempty $w$. The $A$-exponent of periodicity $\mathrm{per}_A(w)$ is defined in the same way with $u$ restricted to single letters $u \in A$; it is the length of the longest block $a^\ell$ in $w$, and $0$ for $w = \varepsilon$.

For a word equation $U = V$ over $A$ that has a nonerasing solution, its exponent of periodicity is

$$
\mathrm{per}(U = V) = \max \{ \mathrm{per}(\sigma(U)) : \sigma \text{ a length-minimal solution of } U = V \},
$$

a maximum over a finite nonempty set, and its $A$-exponent of periodicity is defined in the same way with $\mathrm{per}_A$. For an equation without nonerasing solutions, such as $X = \varepsilon$, neither quantity is defined.

## Depends on

- [Length-minimal solution of a word equation](length-minimal-solution.md)

## Proof depends on

None.

## Expansion

The candidate set in the definition of $\mathrm{per}(w)$ is bounded by $|w|$, because $u^k$ with $u \neq \varepsilon$ is a factor of $w$ only for $k \le |w|$; including $0$ makes the maximum exist also for the empty word and for the empty alphabet. The maximum over length-minimal solutions exists because an equation with a nonerasing solution has finitely many, and at least one, length-minimal solutions.

## Sources

- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Definition 5 (Section 8, "Exponent of periodicity"); the informal definition is in Section 1
- Volker Diekert, "Makanin's Algorithm for Solving Word Equations with Regular Constraints", Report Nr. 1998/02, Fakultät Informatik, Universität Stuttgart (1998), https://elib.uni-stuttgart.de/server/api/core/bitstreams/3846bd76-7ca9-4e0d-8595-75cc76db3018/content; with minor modifications Chapter 12, "Makanin's Algorithm", of M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge University Press (2002), 387–442, https://doi.org/10.1017/CBO9781107326019.013, Definition 2.4 (Section 2.2), the same notion written $\exp(w)$
