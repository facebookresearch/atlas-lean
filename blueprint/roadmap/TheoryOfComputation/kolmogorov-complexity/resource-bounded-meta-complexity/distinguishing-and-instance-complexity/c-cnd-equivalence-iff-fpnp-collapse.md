# C, CD and CND complexity coincide iff FP^NP[log] = FP^NP_tt

Polynomial-time nondeterministic distinguishing complexity matches deterministic generating or distinguishing complexity up to a logarithmic additive term exactly when logarithmically many adaptive NP queries compute the same functions as polynomially many nonadaptive ones (Buhrman, Fortnow and Laplante).

Let $\mathrm{FP}^{\mathrm{NP}[\log n]}$ be the class of functions computable in polynomial time with at most $c\log n$ adaptive queries to an NP oracle, for some constant $c$, and $\mathrm{FP}^{\mathrm{NP}}_{tt}$ the class of functions computable in polynomial time with nonadaptive queries to an NP oracle. $\mathrm{CND}^p$ is the nondeterministic distinguishing complexity of Buhrman, Fortnow and Laplante. The following are equivalent:

1. For every polynomial $p_2$ there are a polynomial $p_1$ and a constant $c$ such that $C^{p_1}(x\mid y)\le\mathrm{CND}^{p_2}(x\mid y)+c\log(|x|+|y|)$ for all $x,y$.
2. For every polynomial $p_2$ there are a polynomial $p_1$ and a constant $c$ such that $\mathrm{CD}^{p_1}(x\mid y)\le\mathrm{CND}^{p_2}(x\mid y)+c\log(|x|+|y|)$ for all $x,y$.
3. $\mathrm{FP}^{\mathrm{NP}[\log n]}=\mathrm{FP}^{\mathrm{NP}}_{tt}$.

## Expansion

Item 1 implies item 2 because generating a string lets one distinguish it. For item 2 implies item 3 the proof uses Lozano's criterion: the collapse holds iff for every $f\in\mathrm{FP}^{\mathrm{NP}}_{tt}$ some $g\in\mathrm{FP}$ outputs a polynomial-size set containing $f(x)$. If $f(x)=y$ asks the query list $Q$ and $w=|Q\cap\mathrm{SAT}|$, a nondeterministic program that knows $w$ guesses $w$ queries with satisfying assignments and recomputes $f(x)$ with the remaining queries answered no; it accepts only $y$, so $y$ and its prefixes have $\mathrm{CND}^p(\cdot\mid x)=O(\log|x|)$. Item 2 turns this into $\mathrm{CD}$ complexity $O(\log|x|)$ for the prefixes, and running all short distinguishers produces the required polynomial list.

## Depends on

- [Distinguishing complexity CD^t](distinguishing-complexity-cdt.md)
- [Nondeterministic time-bounded Kolmogorov complexity nK^t](../nondeterministic-kolmogorov-complexity/nondeterministic-time-bounded-complexity.md)

## Proof depends on

None.

## Sources

- Harry Buhrman, Lance Fortnow and Sophie Laplante, "Resource-Bounded Kolmogorov Complexity Revisited", *SIAM Journal on Computing* 31(3), 2001, [doi:10.1137/S009753979834388X](https://doi.org/10.1137/S009753979834388X) (Definition 7.1, Theorem 7.2, Lemma 7.3; numbering of the May 2001 author version).
