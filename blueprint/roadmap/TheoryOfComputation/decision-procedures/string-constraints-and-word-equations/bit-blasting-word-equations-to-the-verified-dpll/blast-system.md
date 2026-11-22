# CNF encoding of a word-equation system at fixed lengths

Let $n \in \mathbb{N}$ and let $E$ be a finite list of word equations $L = R$ over the alphabet $\{0, 1\}$ with variables $x_0, \dots, x_{n-1}$ (each side a finite word over $\{0, 1\} \cup \{x_0, \dots, x_{n-1}\}$). A substitution $\sigma$ assigns a binary word $\sigma(x_i)$ to each variable, and it satisfies $L = R$ if the words obtained from $L$ and $R$ by replacing each $x_i$ with $\sigma(x_i)$ are equal. A length profile is a map $\ell : \{0, \dots, n-1\} \to \mathbb{N}$. The bit-blasting of a word $u$ over $\{0, 1\} \cup \{x_0, \dots, x_{n-1}\}$ at a length profile $\ell$ is the list of literals obtained by replacing each constant $b \in \{0, 1\}$ by the literal $(0, b)$ (variable $0$, polarity true for $1$ and false for $0$) and each variable $x_i$ by the $\ell(i)$ positive literals $(\langle i, 0\rangle + 1, \mathrm{true}), \dots, (\langle i, \ell(i) - 1\rangle + 1, \mathrm{true})$, where $\langle i, p\rangle$ denotes the pairing bijection $\mathbb{N}^2 \to \mathbb{N}$ given by $\langle i, p\rangle = p^2 + i$ if $i < p$ and $\langle i, p\rangle = i^2 + i + p$ otherwise.

The CNF encoding of $E$ at $\ell$ is the list of clauses consisting of the unit clause $\{(0,
\mathrm{true})\}$ (fixing the constant variable $0$ to true), followed, for each equation $L = R$ of $E$
in order, by the equation clauses of the bit-blastings of $L$ and $R$: if these two literal lists have the
same length, the clauses $\{\neg a_k, b_k\}$ and $\{\neg b_k, a_k\}$ for each position $k$ (with $a_k$,
$b_k$ the $k$-th literals and $\neg(v, s) = (v, \lnot s)$), and otherwise a single empty clause. All
equations share the same variables.
