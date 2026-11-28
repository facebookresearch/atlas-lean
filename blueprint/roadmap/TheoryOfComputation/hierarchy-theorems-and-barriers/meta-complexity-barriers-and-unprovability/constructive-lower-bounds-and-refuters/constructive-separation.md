# Refuters and constructive separations

A separation $f \notin \mathcal{C}$ is constructive when, for every algorithm in $\mathcal{C}$, an efficient refuter prints inputs of each length on which that algorithm errs, for infinitely many lengths. The refuter may depend on the algorithm being refuted.

Let $f \colon \{0,1\}^* \to \{0,1\}$ and let $A$ be an algorithm (randomized algorithms are required to have bounded probability gap, and $A(x)$ denotes the answer output with probability at least $2/3$).

- A $\mathsf{P}$-refuter for $f$ against $A$ is a deterministic polynomial-time algorithm $R$ that on input $1^n$ prints $x \in \{0,1\}^n$ such that for infinitely many $n$, $A(x) \ne f(x)$.
- A $\mathsf{BPP}$-refuter is a randomized polynomial-time $R$ that on input $1^n$ prints $x \in \{0,1\}^n$ such that for infinitely many $n$, $A(x) \ne f(x)$ with probability at least $2/3$.
- A $\mathsf{ZPP}$-refuter is a randomized polynomial-time $R$ that on input $1^n$ prints $x \in \{0,1\}^n \cup \{\perp\}$ such that for infinitely many $n$, with probability $1$ either $x = \perp$ or $A(x) \ne f(x)$, and $x \ne \perp$ with probability at least $2/3$.

For $\mathcal{D} \in \{\mathsf{P}, \mathsf{BPP}, \mathsf{ZPP}\}$ and a typical class $\mathcal{C}$ (one of $\mathsf{P}$, $\mathsf{BPP}$, $\mathsf{ZPP}$, $\mathsf{NP}$, $\Sigma_k\mathsf{P}$, $\mathsf{PP}$, $\oplus\mathsf{P}$, $\mathsf{PSPACE}$, $\mathsf{EXP}$, $\mathsf{NEXP}$, $\mathsf{EXP}^{\mathsf{NP}}$ or a complement), there is a $\mathcal{D}$-constructive separation of $f \notin \mathcal{C}$ if for every algorithm $A$ computable in $\mathcal{C}$ there is a refuter for $f$ against $A$ computable in $\mathcal{D}$. A list-refuter on input $1^n$ outputs a list of strings in $\{0,1\}^n$, at least one of which is a counterexample.

## Context

The output length requirement $|R(1^n)| = n$ matters: with outputs of length $\log n$ the refuter would have time exponential in its output and the task would become easy. The notion goes back to Kabanets' refuters in derandomization and is close to the Chen–Tell–Williams [refuters against a class](../../../pseudorandomness-and-one-way-functions/instance-wise-hardness-versus-randomness/refuter-for-a-function.md), which receive the code of the algorithm; here one fixed refuter is required per algorithm and only infinitely many lengths. Unlike relativization, algebrization and naturalization, constructivity is a property that lower bound proofs should have.

## Depends on

- [The class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [ZPP](../../../complexity-classes/time-and-space-complexity-classes/zpp.md)

## Proof depends on

None.

## Sources

- Lijie Chen, Ce Jin, Rahul Santhanam and Ryan Williams, "Constructive Separations and Their Consequences", *TheoretiCS* 3, 2024 (conference version FOCS 2021), DOI 10.46298/theoretics.24.3, arXiv:2203.14379v5 (Definition 1.1, Refuters and constructive separation, Section 1; list-refuters in Section 1.2, before Theorem 1.7).
