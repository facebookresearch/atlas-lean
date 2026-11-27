# If MKtP ∈ P then polynomial-time K^t is close to Levin Kt

If Levin's Kt complexity can be computed in polynomial time, then for every string the polynomial-time-bounded complexity $K^t(x)$ exceeds $\mathrm{Kt}(x)$ by only $O(\sqrt{\mathrm{Kt}(x)\log n}+\log^2n)$. Derandomization of uniform exponential-time algorithms is equivalent to lower bounds for approximating Kt.

Here Levin's complexity is taken in the bitwise form $\mathrm{Kt}(x)=\min\{|d|+t'+2 : U^d(i)\text{ outputs } x_i\text{ in time }2^{t'}\text{ for every } i\in[|x|+1]\}$, with $x_{|x|+1}$ an end marker, while $K^t(x)$ is the length of a shortest program that prints the whole string $x$ within $t$ steps; since $t\ge\mathrm{poly}(n)$, the statements below do not depend on this choice.

1. If $\mathrm{MKtP}\in\mathrm{P}$, there is a coRP algorithm that, given $x\in\{0,1\}^n$ and $s\in\mathbb{N}$, distinguishes $\mathrm{Kt}(x)\le s$ from $K^t(x)\ge s+O(\sqrt{s\log n}+\log^2n)$, where $t=\mathrm{poly}(n)$.
2. If $\mathrm{MKtP}\in\mathrm{P}$, then $K^t(x)\le\mathrm{Kt}(x)+O(\sqrt{\mathrm{Kt}(x)\log n}+\log^2n)$ for every $x\in\{0,1\}^n$ and every $t\ge\mathrm{poly}(n)$.
3. For every constant $0<\varepsilon<1$, writing $N$ for the input length, the following are equivalent: a derandomization algorithm for $\mathrm{DTIME}(2^{O(\sqrt{N\log N})})$ running in time $2^{N-\omega(\sqrt{N\log N})}$ exists; $\mathrm{MKtP}[N-\omega(\sqrt{N\log N}),N-1]\notin\mathrm{DTIME}(2^{O(\sqrt{N\log N})})$; $\mathrm{MKtP}[N^\varepsilon,N^\varepsilon+\omega(\sqrt{N^\varepsilon\log N})]\notin\mathrm{DTIME}(2^{O(\sqrt{N^\varepsilon\log N})})$.

Since $\mathrm{Kt}(x)\le K^{\mathrm{poly}(n)}(x)+O(\log n)$ holds unconditionally, item 2 says that under $\mathrm{MKtP}\in\mathrm{P}$ the two measures nearly coincide.

## Expansion

Item 2 follows from item 1 by setting $s=\mathrm{Kt}(x)$: a coRP algorithm accepts every yes-instance, so the promise problem must be disjoint, which is the claimed inequality. Item 1 applies the meta-computational view of pseudorandom generator constructions to Kt: an algorithm for MKtP distinguishes the outputs of a reconstructive generator built from $x$ from random strings, and the reconstruction yields a polynomial-time description of $x$ whose length exceeds $\mathrm{Kt}(x)$ by the stated error. Item 3 relies on the universal time-bounded hitting set generator whose image contains every string of Kt complexity at most its seed length.

## Depends on

- [The minimum Kt problem MKtP](../../time-bounded-kolmogorov-complexity/the-minimum-kt-problem.md)
- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Proof depends on

None.

## Sources

- Shuichi Hirahara, "Non-Disjoint Promise Problems from Meta-Computational View of Pseudorandom Generator Constructions", *35th Computational Complexity Conference (CCC 2020)*, LIPIcs 169, 2020, [doi:10.4230/LIPIcs.CCC.2020.20](https://doi.org/10.4230/LIPIcs.CCC.2020.20) (Theorems 14 and 15, Corollary 16, Definitions 36 and 37, Proposition 38).
