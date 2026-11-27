# Braverman's real gate approximators

Over $\mathbb{R}$, the conjunction of bits $b_1,\dots,b_K$ is approximated by the polynomial $\prod_{c=1}^{t}\bigl(1-\sum_{j\in S_c}(1-b_j)\bigr)$ for a random family of subsets $S_1,\dots,S_t\subseteq\{1,\dots,K\}$: $t=s\log K$ random subsets, at least $s$ of them including each element independently with probability $p$ for each $p=2^{-1},2^{-2},\dots,1/K$, together with the full set $\{1,\dots,K\}$; disjunctions are handled dually. The polynomial always equals the conjunction when all $b_j=1$, and for every fixed input it is wrong with probability at most $0.82^{s}$ over the sets. Hence for every input distribution $\nu$ some fixed choice of sets gives an approximator of degree $s\log K$ that agrees with the gate except on $\nu$-mass $0.82^{s}$. Composing approximators over a circuit of depth $d$ and size $m$ yields a polynomial of degree $(s\log m)^d$ that agrees with the circuit except on $\nu$-mass less than $0.82^{s}m$; moreover the indicator of the disagreement set is computed by a Boolean circuit of depth below $d+3$ and size $O(m^2(s\log m)^d)$.

## Proof sketch

This is the probabilistic-polynomial construction of Razborov, Smolensky, Beigel–Reingold–Spielman and Tarui carried out over the reals. If $z\ge1$ of the $b_j$ are $0$ and $2^\alpha\le z<2^{\alpha+1}$, a random subset of density $2^{-\alpha-1}$ catches exactly one zero, making its factor vanish, with probability above $1/(2e)>0.18$; with $s$ such subsets the failure probability is at most $0.82^{s}$. A union bound over the gates gives the circuit bound, and checking that no chosen set contains exactly one zero yields the error indicator.

## Depends on

- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)

## Sources

- Mark Braverman, "Polylogarithmic Independence Fools AC^0 Circuits", Journal of the ACM 57(5), Article 28, 2010 (Lemma 8).
- Alexander A. Razborov, "Lower Bounds on the Size of Bounded Depth Circuits over a Complete Basis with Logical Addition", Mathematical Notes of the Academy of Sciences of the USSR 41(4), 1987.
- Jun Tarui, "Probabilistic Polynomials, AC0 Functions and the Polynomial-Time Hierarchy", Theoretical Computer Science 113(1), 1993.
