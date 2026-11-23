# Linear size bound for bit-blasted words

Let $n, B \in \mathbb{N}$, let $\ell : \{0, \dots, n-1\} \to \mathbb{N}$ satisfy $\ell(i) \le B$ for all
$i$, and let $u$ be a finite word over $\{0, 1\} \cup \{x_0, \dots, x_{n-1}\}$. The bit-blasting of a word $u$ over $\{0, 1\} \cup \{x_0, \dots, x_{n-1}\}$ at a length profile $\ell$ is the list of literals obtained by replacing each constant $b \in \{0, 1\}$ by the literal $(0, b)$ (variable $0$, polarity true for $1$ and false for $0$) and each variable $x_i$ by the $\ell(i)$ positive literals $(\langle i, 0\rangle + 1, \mathrm{true}), \dots, (\langle i, \ell(i) - 1\rangle + 1, \mathrm{true})$, where $\langle i, p\rangle$ denotes the pairing bijection $\mathbb{N}^2 \to \mathbb{N}$ given by $\langle i, p\rangle = p^2 + i$ if $i < p$ and $\langle i, p\rangle = i^2 + i + p$ otherwise. Then the bit-blasting of
$u$ at $\ell$ has at most $\max(1, B) \cdot |u|$ literals.
