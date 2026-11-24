# Decoding string values from a SAT assignment

Let $n \in \mathbb{N}$, let $\ell : \{0, \dots, n-1\} \to \mathbb{N}$ be a length profile and let $\nu :
\mathbb{N} \to \{0, 1\}$ be an assignment. The decoded value of variable $x_i$ is the binary word
$\nu(\langle i, 0\rangle + 1)\, \nu(\langle i, 1\rangle + 1) \cdots \nu(\langle i, \ell(i) - 1\rangle + 1)$ of
length $\ell(i)$, where $\langle i, p\rangle$ denotes the pairing bijection $\mathbb{N}^2 \to \mathbb{N}$ given by $\langle i, p\rangle = p^2 + i$ if $i < p$ and $\langle i, p\rangle = i^2 + i + p$ otherwise.
