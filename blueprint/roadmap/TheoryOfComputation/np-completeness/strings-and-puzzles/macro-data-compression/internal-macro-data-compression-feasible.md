# Feasible INTERNAL MACRO DATA COMPRESSION instances

An instance of macro data compression is a quadruple $(k, s, h, B)$ of a natural number $k$ (the alphabet is $\{0, \dots, k - 1\}$), a finite string $s$ of natural numbers, a pointer cost $h \in \mathbb{N}$ and a bound $B \in \mathbb{N}$. A macro string is a finite string of macro symbols, each either a letter $a$ for some $a \in \mathbb{N}$ or a pointer $p_{j+1}$ with index $j \in \mathbb{N}$; letters and pointers are distinct symbols. For $k, m \in \mathbb{N}$, a macro string is over $(k, m)$ when each of its letters is below $k$ and each of its pointers is one of $p_1, \dots, p_m$. Write $|u|$ for the length of a macro string $u$ and $\pi(u)$ for the number of occurrences of pointers in $u$. For a pointer assignment $\sigma$, sending every pointer to a macro string, a replacement step turns $x\, p\, y$, where $p$ is one occurrence of a pointer, into $x\, \sigma(p)\, y$; write $u \Rightarrow^*_\sigma v$ when $v$ arises from $u$ by finitely many (possibly zero) replacement steps. A string over $\mathbb{N}$ is read as the macro string of its letters.

An instance $(k, s, h, B)$ of internal macro data compression is feasible when there is a macro string $C$ over $(k, |s|)$ with

$$|C| + (h \mathbin{\dot{-}} 1)\,\pi(C) \le B$$

and a pointer assignment $\sigma$ such that $\sigma(p_j)$ is a contiguous substring of $C$ for every $j = 1, \dots, |s|$ and $C \Rightarrow^*_\sigma s$: the string $C$ serves as both the compressed string and the dictionary string. Here $\dot{-}$ is truncated subtraction on $\mathbb{N}$.

Feasibility does not require the instance to be well-formed.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR23] INTERNAL MACRO DATA COMPRESSION, p. 232.
- J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
