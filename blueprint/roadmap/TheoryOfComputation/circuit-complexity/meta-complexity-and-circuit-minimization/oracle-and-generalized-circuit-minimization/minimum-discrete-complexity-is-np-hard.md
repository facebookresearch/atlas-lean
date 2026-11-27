# Minimum discrete complexity is NP-hard

Discrete complexity counts the unions, intersections and complements needed to build a target set from given generator sets; circuit size is the special case of the hypercube with the coordinate sets as generators. Computing it, the problem MDCP, is NP-hard under randomized reductions.

**Definition.** Let $V$ be a finite ground set, $\mathcal{B}=\{B_i\}_{i\in[m]}$ a family of nonempty generator sets $B_i\subseteq V$, and $A\subseteq V$. A construction of $A$ from $\mathcal{B}$ is a sequence $B_1,\dots,B_m,E_1,\dots,E_\ell$ of subsets of $V$ with $E_\ell=A$, where each $E_j$ is the union or intersection of two earlier sets or the complement $V\setminus U$ of an earlier set $U$. The *discrete complexity* $D(A\mid\mathcal{B})$ is the least such $\ell$, with $D(B\mid\mathcal{B})=0$ for $B\in\mathcal{B}$. For $f:\{0,1\}^m\to\{0,1\}$, $V=\{0,1\}^m$ and $\mathcal{B}=\{x_1,\dots,x_m\}$ with $x_i=\{w : w_i=1\}$, the number of AND, OR and NOT gates in a smallest circuit for $f$ is exactly $D(f^{-1}(1)\mid\mathcal{B})$.

The *Minimum Discrete Complexity Problem* MDCP takes $n$ in unary (so $V=[n]$), a target $A\subseteq V$, a family $\mathcal{B}$ of nonempty subsets of $V$ and an integer $s$, and accepts iff $D(A\mid\mathcal{B})\le s$. MDCP is in NP and generalizes MCSP.

**Theorem (Ilango–Loff–Oliveira).** MDCP is NP-hard under polynomial-time randomized reductions. The hardness also holds when $V$ is a hypercube $\{0,1\}^m$ and $\mathcal{B}$ contains the coordinate sets $x_1,\dots,x_m$.

## Expansion

The reduction is from $r$-bounded Set Cover, which is NP-hard to approximate. A random critical target set $A$ is built from the sets of the instance so that a cover of size $\ell$ gives $D(A\mid\mathcal{B}_S)\le\ell$, while any construction with $\ell$ operations uses at most $2\ell$ generators and so yields a cover of size at most $2\ell$. These bounds give a gap-preserving randomized reduction. The same technique, with new ideas, proves NP-hardness of multi-output MCSP ([Multi-output MCSP is NP-hard](../../minimum-circuit-size-problem/multi-output-mcsp-np-hard.md)) and of partial-function MCSP.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Circuit complexity of a Boolean function and truth tables](../../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

None.

## Sources

- Rahul Ilango, Bruno Loff, Igor Carboni Oliveira, "NP-Hardness of Circuit Minimization for Multi-Output Functions", *Computational Complexity Conference (CCC)*, 2020, https://doi.org/10.4230/LIPIcs.CCC.2020.22 (Definitions 3 and 7, Theorem 8, Lemmas 9 to 11, Section 3.2).
