# Systems of word equations reduce to one equation

Over an alphabet with at least two letters, every finite system of word equations has exactly the same solutions as one word equation, built from the system in linear time.

Let $A$ be a finite alphabet containing two distinct letters $a \neq b$, let $\mathcal{X}$ be a set of variables, and let $E = \{L_1 = R_1, \dots, L_k = R_k\}$ be a finite system of word equations with $L_i, R_i \in (A \cup \mathcal{X})^*$ and $k \ge 0$. Then a substitution $\sigma : \mathcal{X} \to A^*$ solves every equation of $E$ if and only if it solves the single equation

$$
L_1 a \cdots L_k a\, R_1 \cdots R_k\, L_1 b \cdots L_k b \;=\; R_1 a \cdots R_k a\, L_1 \cdots L_k\, R_1 b \cdots R_k b .
$$

So the two sets of solutions are identical. For $k = 0$ the single equation is $\varepsilon = \varepsilon$. The single equation has $3 \sum_{i} |L_i R_i| + 4k$ symbols (letters and variable occurrences), so it is computed in time linear in the size of the system.

## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)
- [Solution of a word equation](../../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

None.

## Expansion

If $\sigma$ solves every $L_i = R_i$, the two sides have the same image. Conversely, let $\sigma$ solve the single equation and write $\ell_i = \sigma(L_i)$, $r_i = \sigma(R_i)$. The images of the two sides have lengths $2\sum_i |\ell_i| + \sum_i |r_i| + 2k$ and $2 \sum_i |r_i| + \sum_i |\ell_i| + 2k$, so $\sum_i |\ell_i| = \sum_i |r_i|$. Then the prefixes $\ell_1 a \cdots \ell_k a$ and $r_1 a \cdots r_k a$ of the two images have the same length and are equal, and so are the suffixes $\ell_1 b \cdots \ell_k b$ and $r_1 b \cdots r_k b$. If $|\ell_1| < |r_1|$, the first equality makes $\ell_1 a$ a prefix of $r_1$ and the second makes $\ell_1 b$ a prefix of $r_1$, impossible as $a \neq b$; by symmetry $|\ell_1| = |r_1|$, hence $\ell_1 = r_1$. Cancelling and repeating gives $\ell_i = r_i$ for all $i$. This is the elementary fact the source names: $ua$ and $ub$ prefixes of $va$ and $vb$ with $a \neq b$ force $u = v$.

## Sources

- Volker Diekert, "Makanin's Algorithm for Solving Word Equations with Regular Constraints", Report Nr. 1998/02, Fakultät Informatik, Universität Stuttgart (1998), https://elib.uni-stuttgart.de/server/api/core/bitstreams/3846bd76-7ca9-4e0d-8595-75cc76db3018/content; with minor modifications Chapter 12, "Makanin's Algorithm", of M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge University Press (2002), 387–442, https://doi.org/10.1017/CBO9781107326019.013, Proposition 2.9 (Section 2.4, "From a system to a single equation and vice versa"); the proof is left as Problem 2.2
- Aleksi Saarela, "Hardness Results for Constant-Free Pattern Languages and Word Equations", ICALP 2020, LIPIcs 168, Article 140 (2020), https://doi.org/10.4230/LIPIcs.ICALP.2020.140, Section 2 (after the definitions of the satisfiability problems), which records that with at least two constant letters a finite system has a single equation with the same solutions, constructible in polynomial time
