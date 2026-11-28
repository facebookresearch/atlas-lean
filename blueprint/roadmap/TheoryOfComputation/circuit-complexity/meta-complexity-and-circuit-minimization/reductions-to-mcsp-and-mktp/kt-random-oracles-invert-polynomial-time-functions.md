# Dense KT-random oracles invert polynomial-time functions

Any dense oracle that contains only strings of high KT complexity lets a randomized polynomial-time machine invert every polynomial-time computable function on a noticeable fraction of inputs. Inversion also works with an MKTP or an MCSP oracle, so both invert one-way functions.

**Theorem.** Let $L$ be a language containing at least $2^n/n^k$ strings of each length $n$, for some $k$, such that for some $\varepsilon>0$ every $x\in L$ has $\mathrm{KT}(x)\ge|x|^{\varepsilon}$. Let $f(y,x)$ be computable uniformly in time polynomial in $|x|$. Then there are a polynomial-time probabilistic oracle Turing machine $N$ and a polynomial $q$ such that for every $n$ and every $y$

$$\Pr_{|x|=n,\ s}\left[f\bigl(y,N^{L}(y,f(y,x),s)\bigr)=f(y,x)\right]\ge\frac{1}{q(n)},$$

where $x$ is uniform on $\{0,1\}^n$ and $s$ denotes the internal coins of $N$.

The set $R_{\mathrm{KT}}$ of KT-random strings is such a set $L$ and is decidable in polynomial time with an MKTP oracle; Allender and Das note that the theorem can likewise be used with an MCSP oracle. In circuit form: there is a polynomial-time probabilistic machine $M$ with an MKTP oracle such that for every circuit $C$ on $n$ input bits, $\Pr_{\sigma}[C(M(C,C(\sigma)))=C(\sigma)]\ge 1/\mathrm{poly}(n)$.

## Expansion

From a length-doubling generator $G(y,\cdot)$ computed in polynomial time, the Goldreich–Goldwasser–Micali tree construction (as used by Razborov and Rudich) gives a generator with polynomial stretch whose outputs have circuit size, hence KT complexity, polynomial in the seed length. Choosing the stretch so that every output has KT complexity below $|z|^{\varepsilon}$, the set $L$ accepts many uniform strings but no pseudorandom ones, so it distinguishes $G$ from uniform. The Håstad–Impagliazzo–Levin–Luby construction turns any oracle distinguisher for the generator built from $f$ into an oracle inverter for $f$.

Known unstated proof prerequisites needed before this node is ready for formalization:

- Oracle-relativized Håstad–Impagliazzo–Levin–Luby reduction turning an $L$-oracle distinguisher for the generator built from an arbitrary polynomial-time $f_y$ into an $L$-oracle inverter for $f_y$ (Allender–Buhrman–Koucký–van Melkebeek–Ronneburger, journal Theorem 44, applied in the proof of Theorem 45)

## Depends on

- [KT complexity and the minimum KT problem MKTP](kt-complexity-and-mktp.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)

## Proof depends on

- [One-way functions imply adaptively secure pseudorandom functions](../../../pseudorandomness-and-one-way-functions/hard-core-predicates-and-stretch/one-way-functions-imply-pseudorandom-functions.md)
- [Razborov-Rudich: the natural proofs barrier](../../../hierarchy-theorems-and-barriers/natural-proofs-barrier/razborov-rudich-natural-proofs.md)

## Sources

- Eric Allender, Bireswar Das, "Zero Knowledge and Circuit Minimization", *Information and Computation* 256, 2017, https://doi.org/10.1016/j.ic.2017.04.004 (Theorem 1).
- Eric Allender, Harry Buhrman, Michal Koucký, Dieter van Melkebeek, Detlef Ronneburger, "Power from Random Strings", *SIAM Journal on Computing* 35(6), 2006, https://doi.org/10.1137/050628994 (Theorem 24 and Lemma 25 in the ECCC TR02-028 revision 1 edition, cited as Theorem 45 of the journal version by Allender and Das).
- Eric Allender, Joshua A. Grochow, Dieter van Melkebeek, Cristopher Moore, Andrew Morgan, "Minimum Circuit Size, Graph Isomorphism, and Related Problems", *SIAM Journal on Computing* 47(4), 2018, https://doi.org/10.1137/17m1157970, arXiv:1710.09806v1 (Lemma 1).
