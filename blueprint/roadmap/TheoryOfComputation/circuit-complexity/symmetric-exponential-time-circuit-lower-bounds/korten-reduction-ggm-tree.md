# Korten's reduction: from a non-image of the GGM tree, an NP oracle finds a non-image of C

There is a deterministic algorithm with an $\mathrm{NP}$ oracle that, given $C\colon\{0,1\}^n\to\{0,1\}^{2n}$, $T$ and any $f\in\{0,1\}^T\setminus\mathrm{Im}(\mathrm{GGM}_T[C])$, runs in time $\mathrm{poly}(T,n)$ and outputs a $2n$-bit string outside $\mathrm{Im}(C)$. The algorithm assigns $f$ to the leaves and traverses internal vertices bottom up; at each vertex $u$ it assigns the lexicographically first $x$ with $C(x)$ equal to the concatenation of the values of $u$'s children, found with the $\mathrm{NP}$ oracle. If no such $x$ exists, the children's concatenated value is the output. Since $f$ is not in the image, this happens before the root is assigned. For $T=n\cdot 2^{2n+1}$ the concatenation of all $2n$-bit strings is a trivially known non-image.

Its computation history (a partially assigned GGM tree) is deterministic given $(C,f)$, contains the canonical solution, and is locally verifiable: each step is checked by looking at a constant number of vertex values.

## Proof sketch

Correctness: if every internal vertex received a value, the root value $x$ would satisfy $\mathrm{GGM}_T[C](x)=f$. Each oracle query asks whether some $x$ with a given prefix maps to a given $2n$-bit string, an $\mathrm{NP}$ predicate, so prefix search finds the lexicographically first preimage. The choice of the lexicographically first preimage makes the history a function of $(C,f)$ alone.

## Depends on

- [GGM-tree evaluation: every vertex value of the GGM tree GGM_T of C on input x is computable in time Õ(|C| log T)](ggm-tree-vertex-evaluation.md)
- [Polynomial time with an oracle](../../complexity-classes/time-and-space-complexity-classes/pwith-oracle.md)

## Sources

- Oliver Korten, "The Hardest Explicit Construction", FOCS (2021), arXiv:2106.00875.
- Zeyong Li, "Symmetric Exponential Time Requires Near-Maximum Circuit Size: Simplified, Truly Uniform", STOC (2024), arXiv:2310.17762.
