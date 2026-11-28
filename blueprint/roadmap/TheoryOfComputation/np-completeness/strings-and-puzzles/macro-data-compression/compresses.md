# External macro compression of a string within a bound

A macro string is a finite string of macro symbols, each either a letter $a$ for some $a \in \mathbb{N}$ or a pointer $p_{j+1}$ with index $j \in \mathbb{N}$; letters and pointers are distinct symbols. For $k, m \in \mathbb{N}$, a macro string is over $(k, m)$ when each of its letters is below $k$ and each of its pointers is one of $p_1, \dots, p_m$. Write $|u|$ for the length of a macro string $u$ and $\pi(u)$ for the number of occurrences of pointers in $u$. For a pointer assignment $\sigma$, sending every pointer to a macro string, a replacement step turns $x\, p\, y$, where $p$ is one occurrence of a pointer, into $x\, \sigma(p)\, y$; write $u \Rightarrow^*_\sigma v$ when $v$ arises from $u$ by finitely many (possibly zero) replacement steps. A string over $\mathbb{N}$ is read as the macro string of its letters.

For $k \in \mathbb{N}$, a finite string $s$ over $\mathbb{N}$ and $c, B \in \mathbb{N}$, the string $s$ has an external macro compression with pointer cost $c$ within the bound $B$ when there are macro strings $D$ (the dictionary string) and $C$ (the compressed string), both over $(k, |s|)$, with

$$|D| + |C| + (c \mathbin{\dot{-}} 1)\,\big(\pi(D) + \pi(C)\big) \le B,$$

and a pointer assignment $\sigma$ such that $\sigma(p_j)$ is a contiguous substring of $D$ for every $j = 1, \dots, |s|$ and $C \Rightarrow^*_\sigma s$. Here $\dot{-}$ is truncated subtraction on $\mathbb{N}$, so the pointer surcharge is $0$ when $c = 0$.

Pointers in substrings of $D$ are replaced in turn by later steps.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR22] EXTERNAL MACRO DATA COMPRESSION, p. 231.
- J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
