# Babai's theorem: graph isomorphism in quasipolynomial time

The quasipolynomial graph
isomorphism statement holds: there are a function $D$ from pairs of graph codes to Booleans, an
exponent $c \in \mathbb{N}$, and a deterministic multi-stack Turing machine with a time function
$t : \mathbb{N} \to \mathbb{N}$ that, on the bit encoding of every pair $(G, H)$, outputs the
single bit $D(G, H)$ within $t(\ell)$ steps, where $\ell$ is the length of the encoding, such that
$t(n) \le 2^{(\lfloor \log_2(n+2) \rfloor + 2)^c}$ for every $n \in \mathbb{N}$, and $D(G, H)$ is
true if and only if $G$ and $H$ are isomorphic.

Babai (STOC 2016) gave a deterministic quasipolynomial-time graph-isomorphism algorithm; the
corrected proof retains that complexity.

## Sources

- Babai, L., Graph isomorphism in quasipolynomial time, Proc. 48th ACM Symp. Theory Comput. (STOC 2016), 684-697; arXiv:1512.03547, https://arxiv.org/abs/1512.03547.
