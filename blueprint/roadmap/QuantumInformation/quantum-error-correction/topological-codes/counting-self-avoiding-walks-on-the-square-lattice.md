# Counting self-avoiding walks on the square lattice

Let $c_\ell$ be the number of self-avoiding walks of length $\ell$ on the square lattice $\mathbb{Z}^2$ starting at a
fixed vertex: sequences of $\ell + 1$ distinct vertices, consecutive ones adjacent. Then $c_\ell \le 4 \cdot 3^{\ell - 1}$,
since the first step has $4$ choices and each later step at most $3$; and $c_\ell \le \mu^{\ell} e^{O(\sqrt{\ell})}$, where
$\mu = \lim_\ell c_\ell^{1/\ell} \approx 2.638$ is the connective constant of $\mathbb{Z}^2$. In $d$ dimensions the first
bound is $2d (2d - 1)^{\ell - 1}$. A homologically nontrivial self-avoiding closed path of length $\ell$ on the
$L \times L$ torus lifts to a self-avoiding walk of length $\ell$ on $\mathbb{Z}^2$, which is why these walks, and not only
closed polygons, bound the failure probability of minimum-weight decoding.

## Expansion

A sound expansion adds the definition of the connective constant, whose limit exists by submultiplicativity of $c_\ell$
(Fekete's lemma), and the Hammersley–Welsh bound $c_\ell \le \mu^{\ell} e^{O(\sqrt{\ell})}$ with its source (Madras and
Slade, *The Self-Avoiding Walk*, cited by Dennis, Kitaev, Landahl and Preskill). The elementary bound
$4 \cdot 3^{\ell - 1}$ needs no prerequisite and already gives a threshold with $\mu$ replaced by $3$.

## Sources

- H. Duminil-Copin, S. Ganguly, A. Hammond and I. Manolescu, *Bounding the number of self-avoiding walks: Hammersley–Welsh with polygon insertion*, arXiv:1809.00760, Theorem 1.1 (the Hammersley–Welsh bound $|\mathrm{SAW}_n| \le e^{C n^{1/2}} \mu^n$ for open walks).
- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V.C, equations (56)–(58), which state these bounds for self-avoiding polygons, and Section VI (the count $n_{\mathrm{SAW}}(\ell)$ of self-avoiding walks).
