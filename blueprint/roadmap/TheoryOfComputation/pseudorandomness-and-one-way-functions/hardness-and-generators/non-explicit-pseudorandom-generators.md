# Non-explicit pseudorandom generators of exponential stretch exist

For all $m\in\mathbb{N}$ and $\varepsilon>0$ there is a (non-explicit) function $G:\{0,1\}^{d}\to\{0,1\}^{m}$ with seed length $d=O(\log m+\log(1/\varepsilon))$ such that for every Boolean circuit $C$ of size at most $m$, $\bigl|\Pr_{z}[C(G(z))=1]-\Pr_{u}[C(u)=1]\bigr|\le\varepsilon$ for uniform $z\in\{0,1\}^{d}$ and $u\in\{0,1\}^{m}$. Thus seed length logarithmic in the output length suffices against circuits of size equal to the output length.

## Proof sketch

Choose $G$ uniformly at random. For a fixed circuit $C$ of size $m$, a Chernoff bound shows that $C$ distinguishes $G(U_d)$ from $U_m$ with advantage $\varepsilon$ with probability at most $2^{-\Omega(2^{d}\varepsilon^{2})}$; there are $2^{\mathrm{poly}(m)}$ such circuits, so a union bound leaves a good $G$ once $d=O(\log m+\log(1/\varepsilon))$.

Derived (an explicit-parameter form not stated in the cited sources): there is $G$ with $|G(z)|=S(|z|)$, $S(\ell)=\lceil 2^{\ell/10}\rceil$ for $\ell\ge2$ (and $S(\ell)=\ell$ for $\ell\le1$), fooling every De Morgan circuit with at most $S(\ell)^{3}$ gates with advantage below $1/10$. While $S(\ell)\le\ell$, output the first $S(\ell)$ seed bits, which are exactly uniform. Otherwise choose $G$ on seeds of length $\ell$ at random: by Hoeffding's inequality a fixed circuit's acceptance frequency on the $2^{\ell}$ outputs deviates by $1/10$ with probability at most $2\exp(-2^{\ell}/50)$, and there are $2^{O(S^3\log S)}=2^{o(2^{\ell})}$ circuits of size $S^3$. For seed length $\ell\le1$ every map $\{0,1\}^{\ell}\to\{0,1\}^{\ell+1}$ is distinguished with advantage at least $1/2$ by a linear-size circuit testing membership in its image.

## Depends on

- [Pseudorandom generators against circuits](../derandomization/pseudorandom-generators-against-circuits.md)

## Sources

- Salil P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1–3), 1–336, 2012 (author's copy), Definition 7.3 and Proposition 7.8 ("For all $m \in \mathbb{N}$ and $\varepsilon > 0$, there exists a (nonexplicit) $(m, \varepsilon)$ pseudorandom generator $G : \{0,1\}^d \to \{0,1\}^m$ with seed length $d = O(\log m + \log(1/\varepsilon))$").
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 20 (supplementary; Chapter 16, Exercise 2 of the January 2007 web draft).
