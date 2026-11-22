# Matrix encoded by a list of entries

Number the pairs $(a, b)$ with $a, b \in \{0, 1\}$
by $2a + b$, and index the rows and columns of a $4 \times 4$ complex matrix by these pairs.
Given a list $e$ of pairs of encoded rational numbers, the matrix of $e$ has in row $p$ and
column $q$ the complex number whose real part is the first and whose imaginary part is the
second rational of the entry of $e$ at position $4p + q$ (counting from $0$, with $p$ and $q$
replaced by their numbers), and $0$ when $e$ has no entry at that position. A list of $16$
pairs thus lists the entries in row-major order.

## Sources

- A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum Computation, American Mathematical Society, 2002, Section 14.4.
