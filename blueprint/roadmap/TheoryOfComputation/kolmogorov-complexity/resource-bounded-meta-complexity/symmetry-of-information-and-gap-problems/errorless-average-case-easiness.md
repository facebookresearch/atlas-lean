# Errorless average-case easiness: DistNP ⊆ AvgP, AvgBPP and Heuristica

$\mathrm{DistNP}\subseteq\mathrm{AvgP}$ says that every NP language, under every polynomial-time samplable distribution, has an errorless heuristic scheme: an algorithm that never answers wrongly, may output a failure symbol $\bot$, and fails on at most a $\delta$ fraction of inputs in time polynomial in $n/\delta$.

**Distributional problems.** A distributional problem is a pair $(L,D)$ with $L\subseteq\{0,1\}^*$ and $D=\{D_n\}_{n\in\mathbb{N}}$, each $D_n$ a distribution over $\{0,1\}^*$. The family $D$ is polynomial-time samplable if a randomized polynomial-time algorithm on input $1^n$ outputs a string distributed according to $D_n$; output lengths need not equal $n$. For a class $\mathcal{C}$ of languages, $\mathrm{Dist}\mathcal{C}$ is the set of $(L,D)$ with $L\in\mathcal{C}$ and $D$ polynomial-time samplable. This gives $\mathrm{DistNP}$, $\mathrm{DistPH}$, $\mathrm{Dist}\Sigma_2^p$ and, for an oracle $A$, $\mathrm{DistNP}^A$ (with $L\in\mathrm{NP}^A$).

**Errorless heuristic schemes and AvgP.** A deterministic algorithm $\mathcal{A}(x;n,\delta)$ is a (fully polynomial-time) errorless heuristic scheme for $(L,D)$ if there is a polynomial $p$ such that for every $n$ and every $\delta>0$:

1. for every $x$ in the support of $D_n$, $\mathcal{A}(x;n,\delta)$ outputs $L(x)$ or $\bot$, within $p(n/\delta)$ steps;
2. $\Pr_{x\sim D_n}[\mathcal{A}(x;n,\delta)=\bot]\le\delta$.

$\mathrm{AvgP}$ is the class of distributional problems that admit an errorless heuristic scheme, and $\mathcal{C}_1\subseteq\mathrm{AvgP}$ for a class $\mathcal{C}_1$ of distributional problems means every member of $\mathcal{C}_1$ is in $\mathrm{AvgP}$. In $\mathrm{DistNP}^A\subseteq\mathrm{AvgP}$ the heuristic schemes get no oracle. Replacing condition 1 by $\Pr_{x\sim D_n}[\mathcal{A}(x;n,\delta)\ne L(x)]\le\delta$, with the same time bound, defines an error-prone heuristic scheme and the class $\mathrm{HeurP}$.

**Randomized errorless heuristic schemes and AvgBPP** (in the form used by Hu, Lu and Oliveira). $(L,D)\in\mathrm{AvgBPP}$ if there is a probabilistic polynomial-time algorithm $\mathcal{A}$ such that for all $n,k\in\mathbb{N}$:

1. for every $x$ in the support of $D_n$, $\Pr_{\mathcal{A}}[\mathcal{A}(x,1^n,1^k)\in\{L(x),\bot\}]\ge 4/5$;
2. $\Pr_{x\sim D_n}\bigl[\Pr_{\mathcal{A}}[\mathcal{A}(x,1^n,1^k)=\bot]<1/5\bigr]\ge 1-1/k$.

For the problem $\mathrm{MINnKT}$ with inputs $(x,1^s,1^t)$, $(\mathrm{MINnKT},\mathcal{U})\in\mathrm{AvgBPP}$ means: there are a probabilistic polynomial-time $\mathcal{A}$ and a polynomial $\rho$ such that for all $n,s,k$ and all $t\ge\rho(n)$, every $x\in\{0,1\}^n$ satisfies $\Pr_{\mathcal{A}}[\mathcal{A}(x,1^s,1^t,1^k)\in\{\mathrm{MINnKT}(x,1^s,1^t),\bot\}]\ge 4/5$, and $\Pr_{x\sim\{0,1\}^n}\bigl[\Pr_{\mathcal{A}}[\mathcal{A}(x,1^s,1^t,1^k)=\bot]<1/5\bigr]\ge 1-1/k$.

**Heuristica (Hirahara's sense).** Heuristica is the statement that $\mathrm{P}\ne\mathrm{NP}$ and $\mathrm{DistNP}\subseteq\mathrm{AvgP}$. This uses errorless schemes, and differs from the five-worlds notion built on one polynomial-time algorithm that may answer wrongly on a negligible fraction of inputs; theorems citing this page assume the errorless notion.

## Expansion

Errorless schemes are equivalent to algorithms of average polynomial running time in Levin's sense: run the scheme with $\delta=1/2,1/4,\dots$ until it does not fail, and conversely stop an average-polynomial-time algorithm after $(p(n)/\delta)^{1/\varepsilon}$ steps and output $\bot$. An errorless scheme becomes an error-prone one by answering $0$ in place of $\bot$, so $\mathrm{AvgP}$-membership implies $\mathrm{HeurP}$-membership.

## Depends on

- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [NP relative to an oracle](../../../complexity-classes/time-and-space-complexity-classes/npwith-oracle.md)
- [The polynomial hierarchy](../../../complexity-classes/time-and-space-complexity-classes/ph.md)

## Proof depends on

None.

## Sources

- Andrej Bogdanov and Luca Trevisan, "Average-Case Complexity", *Foundations and Trends in Theoretical Computer Science* 2(1), 2006, [doi:10.1561/0400000004](https://doi.org/10.1561/0400000004) (Definitions 6 and 8, Proposition 7, Definitions 10 to 13; numbering of arXiv:cs/0606037v2).
- Shuichi Hirahara, "Symmetry of Information from Meta-Complexity", *37th Computational Complexity Conference (CCC 2022)*, LIPIcs 234, 2022, [doi:10.4230/LIPIcs.CCC.2022.26](https://doi.org/10.4230/LIPIcs.CCC.2022.26) (Section 1.1, paragraph after Theorem 1.2; Section 1.2).
- Shuichi Hirahara, "Non-Disjoint Promise Problems from Meta-Computational View of Pseudorandom Generator Constructions", *35th Computational Complexity Conference (CCC 2020)*, LIPIcs 169, 2020, [doi:10.4230/LIPIcs.CCC.2020.20](https://doi.org/10.4230/LIPIcs.CCC.2020.20) (Section 1.2, Theorem 4, Corollary 5).
- Jinqiao Hu, Zhenjian Lu and Igor C. Oliveira, "Hardness of Computing Nondeterministic Kolmogorov Complexity", *41st Computational Complexity Conference (CCC 2026)*, LIPIcs, 2026, [doi:10.4230/LIPIcs.CCC.2026.9](https://doi.org/10.4230/LIPIcs.CCC.2026.9) (Section 2.7).
