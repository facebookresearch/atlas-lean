# Demi-bits generators make range avoidance hard for nondeterministic algorithms

If a demi-bits generator with linear stretch exists, then range avoidance (given a stretching circuit, output a string outside its range) has no nondeterministic polynomial-time search algorithm. The hard instances are a demi-bits generator followed by a strong seeded extractor or a pairwise independent hash.

**Range avoidance.** $\mathrm{Avoid}$ and its restriction $\mathcal C$-$\mathrm{Avoid}$ to a circuit class are as on [the range avoidance problem](range-avoidance-problem.md); "stretch $n\to m$" means circuits $C:\{0,1\}^n\to\{0,1\}^m$ with $m>n$.

**Nondeterministic search.** A search problem with relation $R$ is in $\mathsf{SearchNP}$ if a nondeterministic polynomial-time machine $M$ satisfies, for every input $x$: if $x$ has a solution, then $M(x)$ has an accepting path and every accepting path outputs some $y$ with $R(x,y)$; if $x$ has no solution, then $M(x)$ has no accepting path. A nondeterministic polynomial-time machine $\mathcal A$ is an **errorless $\mathsf{SearchNP}$ heuristic** for $R$ if every computational path of $\mathcal A(x)$ either outputs $\bot$ or outputs a valid solution $y$ with $R(x,y)$; $\mathcal A$ *solves* $R$ on $x$ if at least one computational path outputs a valid solution, and *fails* on $x$ (written $\mathcal A(x)=\bot$) if every computational path outputs $\bot$.

**Strong seeded extractors.** A polynomial-time computable $\mathrm{Ext}:\{0,1\}^N\times\{0,1\}^d\to\{0,1\}^m$ is a $(k,\epsilon)$-strong seeded extractor if for every random variable $X$ on $\{0,1\}^N$ with $\Pr[X=x]\le 2^{-k}$ for all $x$, the distributions $(U_d,\mathrm{Ext}(X,U_d))$ and $(U_d,U_m)$ have statistical distance at most $\epsilon$.

**Theorem.** Demi-bits generators are computed by polynomial-size circuits (non-uniform circuits allowed) and taken with respect to polynomial-size nondeterministic adversaries, with the security levels of [demi-bits generators](../../../../Logic/proof-theory/simulations-lower-bounds-and-refutation-certificates/demi-bits-generators-and-refuter-problems/demi-bits-generator.md); $\varepsilon$ denotes a constant with $0<\varepsilon<1$.

1. (Main theorem.) If there exists an $\varepsilon$-secure demi-bits generator $G:\{0,1\}^n\to\{0,1\}^{10n}$, then $\mathrm{Avoid}\notin\mathsf{SearchNP}$.
2. (Extractor form.) Let $m>n$, let $G:\{0,1\}^n\to\{0,1\}^N$ be a $1/2$-secure demi-bits generator and let $\mathrm{Ext}:\{0,1\}^N\times\{0,1\}^d\to\{0,1\}^m$ be an $(N-1,2^{-m-1})$-strong seeded extractor, with $N,d\le\mathrm{poly}(m)$. Then $\mathrm{Avoid}$ for polynomial-size circuits of stretch $n\to m$ is not in $\mathsf{SearchNP}$. The hard instances are the circuits $C_r(s)=\mathrm{Ext}(G(s),r)$ for $r\in\{0,1\}^d$.
3. (Hash form.) Let $G:\{0,1\}^n\to\{0,1\}^N$ be a $1/2$-secure demi-bits generator, let $\mathcal H=\{h:\{0,1\}^N\to\{0,1\}^m\}$ be a family of pairwise independent hash functions computable by polynomial-size circuits (so each $h\circ G$ is a polynomial-size circuit), and let $\mathcal A$ be a nondeterministic polynomial-time algorithm. If $N>10m$ and $m>n$, then there exists $h\in\mathcal H$ such that $\mathcal A$ fails to solve $\mathrm{Avoid}$ on the input $h\circ G$. If $G$ is only $\varepsilon$-secure and $\mathcal A$ is an errorless $\mathsf{SearchNP}$ heuristic for $\mathrm{Avoid}$, then for $N\ge 4m$, $m>n$ and $m\ge\log_2(1/(1-\varepsilon))$, $\mathcal A$ fails on $h\circ G$ for at least a $1-2^{-m}$ fraction of $h\in\mathcal H$.
4. (Constant degree.) If there are constants $\epsilon>0$, $d\ge 2$ and a non-uniform family of $1/2$-secure demi-bits generators $g_n:\{0,1\}^n\to\{0,1\}^{n^{1+\epsilon}}$ secure against $\mathsf{NP}/\mathrm{poly}$ with every output bit a degree-$d$ polynomial over $\mathbb F_2$, then there are constants $\epsilon'>0$ and $d'\ge 2$ such that $\mathrm{Avoid}$ for degree-$d'$ $\mathbb F_2$-polynomial circuits of stretch $n\mapsto n^{1+\epsilon'}$ is not in $\mathsf{SearchNP}$.

## Expansion

For item 2, suppose a nondeterministic algorithm $\mathcal A$ solves $\mathrm{Avoid}$. The adversary $\mathcal B(y)$, for $y\in\{0,1\}^N$, guesses $r\in\{0,1\}^d$ and accepts if some branch of $\mathcal A(C_r)$ outputs $\mathrm{Ext}(y,r)$. If $y=G(s)$ then $\mathrm{Ext}(y,r)=C_r(s)$ lies in the range of $C_r$, so $\mathcal B$ rejects every output of $G$. Let $\mathcal A'(r,z)=1$ when some branch of $\mathcal A(C_r)$ outputs $z$; for each $r$ some $z$ qualifies, so $\Pr_{r,z}[\mathcal A'(r,z)=1]\ge 2^{-m}$. By the extractor property, all but at most $2^{N-1}$ strings $y$ satisfy $\Pr_r[\mathcal A'(r,\mathrm{Ext}(y,r))=1]\ge 2^{-m}-2^{-m-1}>0$, so $\mathcal B$ accepts at least half of $\{0,1\}^N$. This contradicts security exactly when the security level is at most $1/2$, which is why items 2 to 4, proved through this argument, assume a $1/2$-secure generator. Item 3 follows from the leftover hash lemma, and item 4 uses an $\mathbb F_2$-linear hash, which keeps the degree of $G$ (the proof takes $d'=d$ and $\epsilon'=\epsilon/2$).

Items 1 and the $\varepsilon$-secure part of 3 come from a later framework that replaces the extractor by a zero-error disperser family. It shows that an errorless nondeterministic heuristic fails on $h\circ G$ with probability at least $1-2^{-m}$ over a pairwise independent $h$ when $N\ge 4m$ and $m>n$, even if $G$ is only a $2^{3m}$-weak demi-bits generator; an $\varepsilon$-secure $G$ is $2^{3m}$-weak once $(1-\varepsilon)2^N\ge 2^{3m}$, and a $\mathsf{SearchNP}$ algorithm for $\mathrm{Avoid}$ is such a heuristic. Item 1 is the case $N=10n$, $m=2n$.

Earlier hardness results for range avoidance needed subexponentially secure indistinguishability obfuscation or nondeterministic hardness of LWE or LPN; this theorem needs only super-polynomial security against nondeterministic adversaries. The same method gives a bounded-arithmetic separation: if a demi-bits generator $G:\{0,1\}^n\to\{0,1\}^{\omega(n)}$ secure against $\mathsf{AM}/O(1)$ exists (the proof again breaks security level $1/2$), then the dual weak pigeonhole principle for polynomial-time functions is not provable in Cook's theory $\mathsf{PV}_1$, so Jeřábek's $\mathsf{APC}_1$ strictly extends $\mathsf{PV}_1$; the proof shows, via KPT witnessing, that no polynomial-time Student wins the Student-Teacher game for $\mathrm{Avoid}$ in $O(1)$ rounds.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)
- [Demi-bits generators](../../../../Logic/proof-theory/simulations-lower-bounds-and-refutation-certificates/demi-bits-generators-and-refuter-problems/demi-bits-generator.md)

## Proof depends on

- [Leftover hash lemma as a strong extractor](../../../pseudorandomness-and-one-way-functions/derandomization/leftover-hash-lemma-as-a-strong-extractor.md)

## Sources

- Hanlin Ren, Yichuan Wang, Yan Zhong, "Hardness of Range Avoidance and Proof Complexity Generators from Demi-Bits", *Innovations in Theoretical Computer Science Conference (ITCS 2026)*, LIPIcs, 2026, doi:10.4230/LIPIcs.ITCS.2026.111; also arXiv:2511.14061v2, https://arxiv.org/abs/2511.14061 (Theorems 1.1, 1.2, 1.5 and 3.1 with its proof, Corollary 3.2, Definitions 2.8 and 2.17, Theorem 2.19, Assumption 2.3, Theorem 4.1; numbering of arXiv v2).
- Xin Li, Hanlin Ren, Yan Zhong, "Many Proof Complexity Generators Inside One Demi-Bits Generator", *FOCS* 2026, arXiv:2609.23228v1, https://arxiv.org/abs/2609.23228 (Definitions 2.1, 2.2 and 2.7, Theorems 4.1 and 4.7).
