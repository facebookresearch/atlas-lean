# Braverman's real gate approximators

Over $\mathbb{R}$, the conjunction of bits $b_1,\dots,b_K$ is approximated by the polynomial $\prod_{c=1}^{t}\bigl(1-\sum_{j\in S_c}(1-b_j)\bigr)$ for a random family of subsets $S_1,\dots,S_t\subseteq\{1,\dots,K\}$: for each $p=2^{-1},2^{-2},\dots,2^{-\lceil\log_2 K\rceil}$, $s$ random subsets including each element independently with probability $p$, together with the full set $\{1,\dots,K\}$, so $t=1+s\lceil\log_2 K\rceil$; disjunctions are handled dually. The polynomial always equals the conjunction when all $b_j=1$, and for every fixed input it is wrong with probability less than $0.82^{s}$ over the sets. Hence for every input distribution $\nu$ some fixed choice of sets gives an approximator of degree at most $1+s\lceil\log_2 K\rceil$ that agrees with the gate except on $\nu$-mass less than $0.82^{s}$ (for $K=1$ this is the degree-$1$ polynomial $b_1$).

Composing approximators over a circuit of depth $d$ with $m$ gates, each of fan-in at most $m$, yields a polynomial $f$ of degree at most $r=(1+s\lceil\log_2 m\rceil)^d$ that agrees with the function $F$ computed by the circuit except on $\nu$-mass less than $0.82^{s}m$. Moreover there is a Boolean circuit $E$ of depth less than $d+3$ and size $O(m^2r)$ such that $\nu\{E=1\}<0.82^{s}m$ and $f(x)=F(x)$ whenever $E(x)=0$. The flag $E$ is one-sided: it fires on a mistake at any gate, which a gate higher up can mask, so it need not be the indicator of the disagreement set $\{x: f(x)\ne F(x)\}$.

## Proof sketch

This is the probabilistic-polynomial construction of Razborov, Smolensky, Beigel–Reingold–Spielman and Tarui carried out over the reals. If $z\ge1$ of the $b_j$ are $0$ and $2^\alpha\le z<2^{\alpha+1}$, a random subset of density $2^{-\alpha-1}$ catches exactly one zero, making its factor vanish, with probability above $1/(2e)>0.18$; when $z=K$ is a power of two the density $1/K$ is used instead, which catches exactly one zero with probability $(1-1/K)^{K-1}\ge 1/e$. With $s$ such subsets the failure probability is less than $0.82^{s}$. A union bound over the gates gives the circuit bound, and checking at every gate that no chosen set contains exactly one zero yields the flag $E$. Braverman's Lemma 8 states the degree as $(s\log m)^d$, budgeting $t=s\log m$ sets at each gate of fan-in $k<m$.

## Depends on

- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)

## Sources

- Mark Braverman, "Polylogarithmic Independence Fools AC^0 Circuits", Journal of the ACM 57(5), Article 28, 2010 (Lemma 8 and its proof).
- Alexander A. Razborov, "Lower Bounds on the Size of Bounded Depth Circuits over a Complete Basis with Logical Addition", Mathematical Notes of the Academy of Sciences of the USSR 41(4), 1987.
- Jun Tarui, "Probabilistic Polynomials, AC0 Functions and the Polynomial-Time Hierarchy", Theoretical Computer Science 113(1), 1993.
