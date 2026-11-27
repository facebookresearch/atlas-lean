# Non-explicit pseudorandom generators of exponential stretch exist

There is a function $G$ on bit strings with $|G(z)|=S(|z|)$, where $S(\ell)=\lceil 2^{\ell/10}\rceil$ for $\ell\ge2$ (and $S(\ell)=\ell$ for $\ell\le1$), such that for every $\ell$ and every De Morgan circuit $C$ with at most $S(\ell)^{3}$ gates, $\bigl|\Pr_{z}[C(G(z))=1]-\Pr_{u}[C(u)=1]\bigr|<1/10$ for uniform $z\in\{0,1\}^{\ell}$ and $u\in\{0,1\}^{S(\ell)}$. On the other hand, for seed length $\ell\le1$ every map $\{0,1\}^{\ell}\to\{0,1\}^{\ell+1}$ is distinguished with advantage at least $1/2$ by a linear-size circuit testing membership in its image.

## Proof sketch

While $S(\ell)\le\ell$ (small $\ell$), output the first $S(\ell)$ seed bits, which are exactly uniform. Otherwise choose $G$ on seeds of length $\ell$ uniformly at random. For a fixed circuit, Hoeffding's inequality bounds the probability that its acceptance frequency on the $2^{\ell}$ outputs deviates by $1/10$ by $2\exp(-2^{\ell}/50)$; the number of circuits of size $S^3$ is $2^{O(S^3\log S)}=2^{o(2^{\ell})}$, so a union bound leaves a good $G$.

## Depends on

- [Pseudorandom generators against circuits](../derandomization/pseudorandom-generators-against-circuits.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 20 (Chapter 16, Exercise 2 of the January 2007 web draft, with the generator definition using circuits of size $S(\ell)^3$ and distinguishing advantage $1/10$).
