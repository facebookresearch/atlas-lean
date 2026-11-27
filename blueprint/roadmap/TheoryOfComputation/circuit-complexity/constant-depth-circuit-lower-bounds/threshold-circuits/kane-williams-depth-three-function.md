# The Kane–Williams function: hardness for depth-two threshold circuits

Let $m$ be a power of two, let $A_{m,n}\in\mathbb{F}_2^{m\times n}$ be a matrix whose rows $r_z$ ($z\in\{0,1\}^{\log_2 m}$) form a small-biased set of vectors in $\mathbb{F}_2^n$ (an explicit $1/\mathrm{poly}(n)$-balanced code), and let $F(z,x)=\langle r_z,x\rangle\bmod2$ be the $z$-th bit of $A_{m,n}x$. For $k\mid n$ and $x,a\in\{0,1\}^n$ (with $m=2^k$), the *Kane–Williams function* is

$$
B_{n,k}(x,a)=F(z,x),\qquad z_i=\bigoplus_{j=(n/k)(i-1)+1}^{(n/k)i}a_j\quad(1\le i\le k),
$$

that is, Andreev's function with the multiplexer replaced by $F$, and $B_n=B_{n,k}$ for $k=16\log_2n$; it is computable in polynomial time. For distinct $x,y$ the columns $F(\cdot,x)$ and $F(\cdot,y)$ agree on a $\tfrac12+O(\sqrt{n/m})$ fraction of $z$, so no fixed string has noticeable correlation with $F(\cdot,x)$ for many $x$; hence some $x$ makes $F(\cdot,x)$ agree with every depth-two weighted threshold circuit of $o(n/\log^2n)$ gates on at most a $\tfrac12+O(n^{1/2})/m^{1/4}$ fraction of inputs. Consequently no majority of depth-two weighted threshold circuits ($\mathrm{MAJ}\circ\mathrm{LTF}\circ\mathrm{LTF}$) with $o(n^{3/2}/\log^3n)$ gates or $o(n^{5/2}/\log^{7/2}n)$ wires computes $B_n$.

## Proof sketch

Fix $x$ to a string as above. Restrict $a$ by the Kane–Williams random restriction that leaves one variable alive in each of the $k$ parity blocks: each bottom threshold gate stays non-constant with probability $O(k/\sqrt n)$, and a bottom gate with $u$ wires fails to become a single wire with probability $O(uk^{3/2}/n^{3/2})$, so some restriction leaves only $o(n/\log^2n)$ nontrivial bottom gates. Then every middle-layer depth-two circuit has correlation at most $O(n^{1/2}2^{-k/4})\ll n^{-3}$ with $B_n$ restricted, so the top majority cannot compute it.

## Depends on

- [Depth-two weighted threshold circuits](depth-two-weighted-threshold-circuits.md)

## Proof depends on

- [Kane–Williams random restriction lemmas for linear threshold functions](kane-williams-random-restriction-lemmas.md)
- [Counting threshold functions over a feature family](counting-threshold-functions.md)

## Sources

- Daniel M. Kane, Ryan Williams, "Super-Linear Gate and Super-Quadratic Wire Lower Bounds for Depth-Two and Depth-Three Threshold Circuits", Proceedings of the Forty-Eighth Annual ACM Symposium on Theory of Computing (STOC 2016), 2016 (Corollaries 6.1–6.2, Lemma 6.1, Definition 6.1 and Theorem 1.3).
