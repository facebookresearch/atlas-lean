# Jeřábek's theory APC1 and the dual weak pigeonhole principle

$\mathsf{APC}_1$ formalizes probabilistic polynomial-time reasoning by adding to $\mathsf{PV}$ the dual weak pigeonhole principle for all polynomial-time functions: no polynomial-time map from $[N]$ can cover $(1+1/n)N$ values.

$$
\mathsf{APC}_1 = \mathsf{PV} \cup \{\mathsf{dWPHP}(f) : f \in \mathcal{L}_{\mathsf{PV}}\},
$$

where $\mathsf{dWPHP}(f)$ postulates that for every length $n = |N|$ there is $y < (1 + 1/n) N$ with $f(x) \ne y$ for every $x < N$; Pich and Santhanam write it as $x > 0 \rightarrow \exists v < x(|y|+1)\, \forall u < x|y|,\ f(u) \ne v$, where $f$ may involve further parameters. The variant $\mathsf{dWPHP}'(\mathsf{PV})$ forbids parameters other than $u$. The theories $\mathsf{T}_{\mathsf{PV}}$ (all true universal $\mathcal{L}_{\mathsf{PV}}$-sentences), $\mathsf{T}_{\mathsf{APC}_1} = \mathsf{T}_{\mathsf{PV}} + \mathsf{dWPHP}(\mathsf{PV})$ and $\mathsf{T}'_{\mathsf{APC}_1} = \mathsf{T}_{\mathsf{PV}} + \mathsf{dWPHP}'(\mathsf{PV})$ extend this setting, and more generally $\mathsf{T}^i_{\mathsf{PV}}$ is the theory of all true $\forall\Sigma^b_{i-1}$-sentences over $\mathcal{L}_{\mathsf{PV}}$.

The dual weak pigeonhole principle for polynomial-time functions is provable in $\mathsf{T}^2_2$, so $\mathsf{APC}_1 \subseteq \mathsf{T}^2_2(\mathcal{L}_{\mathsf{PV}})$, and every axiom of $\mathsf{APC}_1$ follows from a true $\forall\Sigma^b_2$-sentence, so $\mathsf{APC}_1 \subseteq \mathsf{T}^3_{\mathsf{PV}}$.

## Context

$\mathsf{APC}_1$ proves the existence of a Boolean function hard for small circuits (not known in $\mathsf{PV}$), formalizes approximate counting and the Nisan–Wigderson construction, and proves $\mathsf{AC}^0$, $\mathsf{AC}^0[p]$ and monotone circuit lower bounds without the LogLog convention. It is therefore the natural test case for unconditional unprovability of strong lower bounds.

## Depends on

- [Cook's theory PV of polynomial-time reasoning](cooks-theory-pv.md)

## Proof depends on

None.

## Sources

- Igor C. Oliveira, "SIGACT News Complexity Theory Column 124: Meta-Mathematics of Computational Complexity Theory", *ACM SIGACT News* 56(1), 2025, DOI 10.1145/3726856.3726862, arXiv:2504.04416v1 (Section 2.2.3, APC_1).
- Ján Pich and Rahul Santhanam, "Strong Co-Nondeterministic Lower Bounds for NP Cannot be Proved Feasibly", *STOC* 2021, DOI 10.1145/3406325.3451117 (Sections 2.1 and 3.1, dWPHP, T_PV and T'_APC1, in the authors' full version of March 2021, <https://users.ox.ac.uk/~coml0742/papers/stoc-final.pdf>).
- Jiatu Li and Igor C. Oliveira, "Unprovability of Strong Complexity Lower Bounds in Bounded Arithmetic", *STOC* 2023, DOI 10.1145/3564246.3585144, arXiv:2305.15235v1 (Section 1.1, the theories T^i_PV and the inclusion of APC_1 in T^3_PV).
