# Sipser's coding lemma for distinguishing complexity

With a random auxiliary string, every member of a polynomial-time set $A$ has a polynomial-time distinguishing description of nearly optimal length $\log|A^{=n}|+O(\log n)$. Sipser introduced this lemma for the first proof that BPP lies in the polynomial hierarchy.

For every polynomial-time computable set $A$ there exist a polynomial $p$ and a constant $c$ such that for every $n$, for most strings $r\in\{0,1\}^{p(n)}$, every $x\in A^{=n}$ satisfies

$$
\mathrm{CD}^{p,A}(x\mid r)\le \log|A^{=n}|+c\log n .
$$

In the Buhrman–Fortnow–Laplante proof, "most" means that with probability at least $1/2$ over $r$ the bound holds simultaneously for all $x\in A^{=n}$. Since $A\in\mathrm{P}$, the oracle can be replaced by computation, giving $\mathrm{CD}^p(x\mid r)\le\log|A^{=n}|+c\log n$ as stated by Fortnow.

## Expansion

For each $k\le n$ let $r_k$ list $4k(n+1)$ random numbers below $2^k$, and let $r$ concatenate the lists. Put $d=|A^{=n}|$ and choose $k$ with $2^{k-1}<4dn^2\le 2^k$. Each listed number is, with probability more than $1/(4k)$, a prime below $4dn^2$ that separates a fixed $x$ from the rest of $A^{=n}$, so some entry of $r_k$ works for $x$ except with probability below $2^{-(n+1)}$; a union bound over $A^{=n}$ leaves probability at least $1/2$. The description is a pointer to that entry plus the residue of $x$, of total length $\log d+O(\log n)$. Buhrman, Fortnow and Laplante remove the random string at the cost of a second $\log|A^{=n}|$ term, and derive the Valiant–Vazirani isolation lemma from this lemma.

## Depends on

- [Distinguishing complexity CD^t](distinguishing-complexity-cdt.md)

## Proof depends on

None.

## Sources

- Harry Buhrman, Lance Fortnow and Sophie Laplante, "Resource-Bounded Kolmogorov Complexity Revisited", *SIAM Journal on Computing* 31(3), 2001, [doi:10.1137/S009753979834388X](https://doi.org/10.1137/S009753979834388X) (Lemma 3.6 and Section 3.1; numbering of the May 2001 author version).
- Lance Fortnow, "Kolmogorov Complexity and Computational Complexity", in *Complexity of Computations and Proofs* (J. Krajíček, ed.), Quaderni di Matematica 13, 2004, [author copy](https://lance.fortnow.com/papers/files/quaderni.pdf) (Theorem 4.3).
