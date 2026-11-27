# Members of a set have CD complexity at most twice the log of its size

Every length-$n$ member of any set $A$ has a polynomial-time distinguishing program, using an oracle for $A$, of length $2\log|A^{=n}|+O(\log n)$; for $A\in\mathrm{P}$ no oracle is needed. Relative to an oracle the factor $2$ is tight, and the bound characterizes sparse sets.

Let $A^{=n}=A\cap\{0,1\}^n$.

1. For every set $A$ there is a polynomial $p$ such that for all $n$ and all $x\in A^{=n}$, $\mathrm{CD}^{p,A}(x)\le 2\log|A^{=n}|+O(\log n)$. The same holds for nondeterministic distinguishing complexity $\mathrm{CND}^p$.
2. If $A\in\mathrm{P}$, there is a polynomial $p$ such that every $x\in A$ satisfies $\mathrm{CD}^p(x)\le 2\log|A^{=|x|}|+O(\log|x|)$.
3. (Buhrman, Laplante and Miltersen.) For every polynomial $p$ and all sufficiently large $n$ there is a set $A\subseteq\{0,1\}^n$ with more than $2^{n/50}$ elements containing some $x$ with $\mathrm{CD}^{p,A}(x)\ge 2\log|A^{=n}|-O(1)$.
4. A set $S$ is sparse iff $\mathrm{CD}^{p,S}(x)\le O(\log|x|)$ for all $x\in S$ and some polynomial $p$; a set $S\in\mathrm{P}$ is sparse iff $\mathrm{CD}^{p}(x)\le O(\log|x|)$ for all $x\in S$ and some $p$; a set $S\in\mathrm{NP}$ is sparse iff $\mathrm{CND}^{p}(x)\le O(\log|x|)$ for all $x\in S$ and some $p$.

## Expansion

The key is hashing by a prime modulus: if $S=\{x_1,\dots,x_d\}\subseteq\{0,\dots,2^n-1\}$, then for each $x_i$ at least half of the primes $p\le 4dn^2$ satisfy $x_i\not\equiv x_j \pmod p$ for all $j\ne i$, because $|x_i-x_j|<2^n$ has at most $n$ prime factors and there are more than $2dn$ primes below $4dn^2$. The distinguisher for $x\in A^{=n}$ stores such a prime $p_x$ and the residue $x\bmod p_x$; on input $y$ it rejects unless $y\in A^{=n}$, and accepts iff $y\equiv x\pmod{p_x}$. Both stored numbers have $\log|A^{=n}|+O(\log n)$ bits. For $A\in\mathrm{P}$ membership is computed directly at the cost of encoding $n$. Sparseness follows from item 1 and the counting fact that some member of $A^{=n}$ has complexity at least $\log|A^{=n}|$.

## Depends on

- [Distinguishing complexity CD^t](distinguishing-complexity-cdt.md)
- [Nondeterministic time-bounded Kolmogorov complexity CND^t = nK^t](../nondeterministic-kolmogorov-complexity/nondeterministic-time-bounded-complexity.md)

## Proof depends on

None.

## Sources

- Harry Buhrman, Lance Fortnow and Sophie Laplante, "Resource-Bounded Kolmogorov Complexity Revisited", *SIAM Journal on Computing* 31(3), 2001, [doi:10.1137/S009753979834388X](https://doi.org/10.1137/S009753979834388X) (Lemma 3.1, Lemma 3.2, Theorem 3.3, Corollary 3.4, Corollary 3.5; numbering of the May 2001 author version).
- Lance Fortnow, "Kolmogorov Complexity and Computational Complexity", in *Complexity of Computations and Proofs* (J. Krajíček, ed.), Quaderni di Matematica 13, 2004, [author copy](https://lance.fortnow.com/papers/files/quaderni.pdf) (Theorems 4.4 and 4.5).
