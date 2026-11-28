# Robust algorithms for promise CSPs with majority or alternating-threshold polymorphisms

A Boolean promise CSP whose polymorphisms include majority, or alternating-threshold, functions of all odd arities admits a randomized polynomial-time algorithm that, on instances with an assignment strongly satisfying a $1-\varepsilon$ fraction of constraints, weakly satisfies in expectation a $1-f(\varepsilon)$ fraction, with $f(\varepsilon)\to 0$ and constants depending on the template.

Let $\mathbb{B}=\{-1,+1\}$ and let $\Gamma=\{(P_1,Q_1),\dots,(P_l,Q_l)\}$ be a Boolean promise template with $P_i\subseteq Q_i\subseteq\mathbb{B}^{k_i}$. An instance of the folded idempotent problem $\mathrm{fiPCSP}(\Gamma)$ has variables $u_1,\dots,u_n$ and constraints, each a tuple of literals (variables, negated variables or constants in $\mathbb{B}$) with a predicate pair $(P^{(j)},Q^{(j)})\in\Gamma$; an assignment strongly (weakly) satisfies a constraint if the literal values lie in $P^{(j)}$ ($Q^{(j)}$). An algorithm is $f$-robust if, given an instance and $\varepsilon$ with the promise that some assignment strongly satisfies a $1-\varepsilon$ fraction of constraints, it outputs an assignment weakly satisfying at least a $1-f(\varepsilon)$ fraction; it is robust if it is $f$-robust for a monotone non-negative $f$ with $f(\varepsilon)\to 0$ as $\varepsilon\to 0$. For odd $L$, $\mathrm{MAJ}_L(x)=+1$ iff $x_1+x_2+\dots+x_L>0$ and $\mathrm{AT}_L(x)=+1$ iff $x_1-x_2+x_3-\dots+x_L>0$.

1. If $\mathrm{Pol}(\Gamma)$ contains $\mathrm{MAJ}_L$ for all odd $L$, then for every $\varepsilon>0$ a randomized polynomial-time algorithm, given an instance of $\mathrm{fiPCSP}(\Gamma)$ promised to have an assignment satisfying a $1-\varepsilon$ fraction of the constraints, finds an assignment that satisfies, in expectation, a $1-\tilde O_\Gamma(\varepsilon^{1/3})$ fraction of the constraints.
2. If $\mathrm{Pol}(\Gamma)$ contains $\mathrm{AT}_L$ for all odd $L$, a randomized polynomial-time algorithm, under the same promise, finds an assignment that satisfies, in expectation, a $1-O_\Gamma\left(\frac{\log\log(1/\varepsilon)}{\log(1/\varepsilon)}\right)$ fraction of the constraints.
3. Conversely, if $\Gamma=\{(P,Q)\}$ is a pair of symmetric Boolean predicates and $\mathrm{AT}_{L_1},\mathrm{MAJ}_{L_2}\notin\mathrm{Pol}(\Gamma)$ for some odd $L_1,L_2$, then under the Unique Games Conjecture there is no polynomial-time robust algorithm for $\mathrm{fiPCSP}(\Gamma)$ unless $\mathsf{P}=\mathsf{NP}$.

Here $O_\Gamma$ and $\tilde O_\Gamma$ hide constants depending on $\Gamma$, and $\tilde O$ also hides polylogarithmic factors.

## Expansion

Both algorithms round the basic SDP relaxation without inspecting the predicates, using the polymorphisms as a black box. With MAJ polymorphisms the template reduces to weak predicates of $k$-SAT form, and the Charikar–Makarychev–Makarychev rounding for 2-SAT is reanalyzed through the majority polymorphisms; with AT polymorphisms it reduces to a weighted hyperplane template generalizing (1-in-3-SAT, NAE-3-SAT), handled by random threshold rounding. The hardness direction builds SDP integrality gaps with perfect completeness on the sphere: the infinite instance whose constraints are all tuples of unit vectors satisfying the SDP constraints has no weakly satisfying coloring, by sphere Ramsey theory of Matoušek and Rödl, compactness yields a finite gap, and Raghavendra's theorem converts the gap into Unique-Games hardness of robust satisfaction.

## Depends on

- [Promise constraint satisfaction PCSP(A,B) for a pair of finite templates](promise-csp-of-a-template-pair.md)
- [The polymorphism minion Pol(A,B) of a promise template](polymorphism-minion-of-a-promise-template.md)
- [The Unique Games Conjecture](../../../pcp-and-inapproximability/pcp-constructions/the-unique-games-conjecture.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [The basic SDP relaxation of a generalized CSP](../../../pcp-and-inapproximability/sdp-optimality-and-approximation-resistance/basic-sdp-relaxation.md)
- [Raghavendra's theorem: the basic SDP is UGC-optimal for every CSP](../../../pcp-and-inapproximability/sdp-optimality-and-approximation-resistance/raghavendra-optimality.md)

## Sources

- Joshua Brakensiek, Venkatesan Guruswami and Sai Sandeep, "SDPs and Robust Satisfiability of Promise CSP", *Discrete Analysis* 2025:14, https://doi.org/10.19086/da.143808 (expanded version of the STOC 2023 paper), arXiv:2211.08373v5 (Theorems 4.1 and 4.10 for the precise algorithmic statements, Theorems 1.3 and 1.4, Definitions 2.6 and 2.7, Section 2.2, Theorem 5.2, Lemma 5.6).
