# Pairwise-independent hashing by affine maps over GF(2)

A family $\mathcal{H}$ of functions $\{0,1\}^n \to \{0,1\}^m$ is *pairwise independent* if for all $x \ne x'$ in $\{0,1\}^n$ and all $y, y' \in \{0,1\}^m$,
$\Pr_{h \in \mathcal{H}}[h(x) = y \wedge h(x') = y'] = 2^{-2m}$ for $h$ chosen uniformly from $\mathcal{H}$; equivalently, $(h(x), h(x'))$ is uniform on $\{0,1\}^m \times \{0,1\}^m$.

**Lemma.** Identify $\{0,1\}$ with $\mathbb{F}_2$. For $m, n \ge 1$, the family $\mathcal{H}_{n,m}$ of maps $h_{A,b}(x) = Ax + b$, with $A$ ranging over all $m \times n$ matrices over
$\mathbb{F}_2$ and $b$ over $\mathbb{F}_2^m$, is pairwise independent.

Proof: let $x \ne x'$ and choose $A$ and $b$ independently and uniformly. Since $x - x' \ne 0$, the vector $A(x - x')$ is uniform on $\mathbb{F}_2^m$, and $b$ is
uniform and independent of $A$. The pair $(Ax + b,\, A(x - x'))$ is therefore uniform on $\mathbb{F}_2^m \times \mathbb{F}_2^m$, and $(h(x), h(x'))$ is a bijective image of it.

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08: Definition 8.10 (pairwise independence, with exponent $-2k$ for output length $k$; the draft prints $-2n$) and Exercise 8.4 (the family $h_{A,b}(x) = Ax + b$). The proof is derived on this page.
