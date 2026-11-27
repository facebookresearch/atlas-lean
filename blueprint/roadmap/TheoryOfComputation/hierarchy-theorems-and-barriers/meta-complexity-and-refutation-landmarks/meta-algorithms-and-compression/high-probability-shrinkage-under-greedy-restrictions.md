# High-probability shrinkage of formulas under greedy random restrictions

Repeatedly fixing the most frequent variable of a de Morgan formula to a random bit shrinks it, except with probability below $2^{-k}$, to size at most $2L(F)(k/n)^{3/2}$ once $k$ variables remain; formulas over the complete basis and branching programs shrink with exponent $1$.

Let $F$ be a de Morgan formula on $n$ variables with leaf size $L(F)$, kept simplified by the standard simplification rules that do not change the computed function. Define the adaptive random restriction $F_0=F$ and, for $1\le i\le n$, let $F_i$ be obtained from $F_{i-1}$ by assigning its most frequent variable a uniformly random value in $\{0,1\}$ and simplifying; $F_i$ has $n-i$ unrestricted variables. For every $k\ge 4$,

$$
\Pr\left[L(F_{n-k})\ge 2\cdot L(F)\cdot\left(\frac{k}{n}\right)^{\Gamma}\right]<2^{-k},
$$

with shrinkage exponent $\Gamma=3/2$ for de Morgan formulas and $\Gamma=1$ for formulas over the complete binary basis and for branching programs.

Structural consequence: if $F$ is a formula or branching program of size $O(n^d)$ with $d<2.5$ for de Morgan formulas, or $d<2$ for complete-basis formulas and branching programs, there are constants $0<\delta,\gamma<1$ such that, for $k=\lceil n^{\delta}\rceil$, the function of $F$ is computed by a decision tree of depth $n-k$ whose leaves are labeled by restrictions of $F$, and all but a $2^{-k}$ fraction of the leaf labels are formulas (branching programs) on $k$ variables of size $O(n^{\gamma})$.

## Expansion

One step removes the most frequent variable $x$, which appears at least $L(F)/n$ times; simplification deletes each occurrence, so $L(F_1)\le L(F)(1-1/n)$, and each occurrence's sibling subtree, which avoids $x$, disappears with probability $1/2$, which gives

$$
\mathbb{E}[L(F_1)]\le L(F)\left(1-\frac{1}{n}\right)^{3/2}.
$$

With $l_i=\log L(F_i)$, the centered increments of $l_i$ form a supermartingale whose steps are bounded by $c_i=-\tfrac12\log(1-\tfrac{1}{n-i+1})$, and a concentration bound for supermartingales gives the tail bound. The decision-tree structure yields a deterministic $\#\mathrm{SAT}$ algorithm running in time $2^{n-n^{\delta}}$ for de Morgan formulas of size $n^{d}$ with $d<2.5$ and for complete-basis formulas and branching programs of size $n^{d}$ with $d<2$, and an alternative proof of the Komargodski–Raz average-case lower bound against such formulas.

## Depends on

None.

## Proof depends on

None.

## Sources

- Ruiwen Chen, Valentine Kabanets, Antonina Kolokolova, Ronen Shaltiel and David Zuckerman, "Mining Circuit Lower Bound Proofs for Meta-Algorithms", *Computational Complexity* 24, 2015, https://doi.org/10.1007/s00037-015-0100-0 (Lemma 3.3, Corollary 3.4, Lemmas 4.2 to 4.5, Theorem 5.1).
