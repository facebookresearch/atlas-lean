# The quasipolynomial graph isomorphism statement

The proposition that graph isomorphism
is decidable in quasipolynomial time: there are a function $D$ from pairs of graph codes to
Booleans, an exponent $c \in \mathbb{N}$, and a deterministic multi-stack Turing machine with a
time function $t : \mathbb{N} \to \mathbb{N}$ that, on the bit encoding of every pair $(G, H)$,
outputs the single bit $D(G, H)$ within $t(\ell)$ steps, where $\ell$ is the length of the
encoding, such that $t(n) \le q_c(n)$ for every $n \in \mathbb{N}$, where $q_c$ is the
quasipolynomial time bound with exponent $c$, and $D(G, H)$ is true if and only if $G$ and $H$
are isomorphic.

## Sources

- ALG-016.
