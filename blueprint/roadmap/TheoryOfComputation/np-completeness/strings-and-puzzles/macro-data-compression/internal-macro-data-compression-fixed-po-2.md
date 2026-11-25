# The INTERNAL MACRO DATA COMPRESSION decision problem with a fixed pointer cost

An instance $(k, s, h, B)$ is well-formed when every letter of $s$ is below $k$, $h \ge 1$ and $B \ge 1$. A macro string is a finite string of macro symbols, each either a letter $a$ for some $a \in \mathbb{N}$ or a pointer $p_{j+1}$ with index $j \in \mathbb{N}$; letters and pointers are distinct symbols. For $k, m \in \mathbb{N}$, a macro string is over $(k, m)$ when each of its letters is below $k$ and each of its pointers is one of $p_1, \dots, p_m$. Write $|u|$ for the length of a macro string $u$ and $\pi(u)$ for the number of occurrences of pointers in $u$. For a pointer assignment $\sigma$, sending every pointer to a macro string, a replacement step turns $x\, p\, y$, where $p$ is one occurrence of a pointer, into $x\, \sigma(p)\, y$; write $u \Rightarrow^*_\sigma v$ when $v$ arises from $u$ by finitely many (possibly zero) replacement steps. A string over $\mathbb{N}$ is read as the macro string of its letters.

An instance $(k, s, h, B)$ of internal macro data compression is feasible when there is a macro string $C$ over $(k, |s|)$ with

$$|C| + (h \mathbin{\dot{-}} 1)\,\pi(C) \le B$$

and a pointer assignment $\sigma$ such that $\sigma(p_j)$ is a contiguous substring of $C$ for every $j = 1, \dots, |s|$ and $C \Rightarrow^*_\sigma s$: the string $C$ serves as both the compressed string and the dictionary string. Here $\dot{-}$ is truncated subtraction on $\mathbb{N}$.

For $h \in \mathbb{N}$, the INTERNAL MACRO DATA COMPRESSION decision problem with fixed pointer cost $h$ accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a triple $(k, s, B)$ such that $(k, s, h, B)$ is well-formed and feasible for internal macro data compression. Bitstrings that do not decode to a triple are rejected; for $h = 0$ every bitstring is rejected.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR23] INTERNAL MACRO DATA COMPRESSION, comment: "Remains NP-complete even if $h$ is any fixed integer 2 or greater."
- J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
