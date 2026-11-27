# Compression algorithms imply NEXP circuit lower bounds

If truth tables of functions in a class $\mathcal{C}\subseteq\mathsf{P}/\mathrm{poly}$ can be compressed in polynomial time to circuits smaller than $2^n/n$, then $\mathsf{NEXP}\not\subseteq\mathcal{C}$, complementing Williams' theorem that non-trivial circuit satisfiability algorithms give such lower bounds.

Let $\mathcal{C}\subseteq\mathsf{P}/\mathrm{poly}$ be any circuit class and $\mathcal{C}[n^c]$ its circuits of size $n^c$. Suppose that for every $c\in\mathbb{N}$ there is a deterministic algorithm running in time polynomial in $2^n$ that, given the truth table of an $n$-variate Boolean function $f\in\mathcal{C}[n^c]$, outputs a circuit of size less than $2^n/n$ computing $f$. Then $\mathsf{NEXP}\not\subseteq\mathcal{C}$.

## Expansion

Suppose $\mathsf{NEXP}\subseteq\mathcal{C}$. Refining the Impagliazzo–Kabanets–Wigderson easy-witness argument from $\mathsf{P}/\mathrm{poly}$ to any subclass $\mathcal{C}\subseteq\mathsf{P}/\mathrm{poly}$, there is a constant $c_0$ such that yes-instances of length $n$ of every language in $\mathsf{NE}$ have witnesses that are truth tables of $m=n^2$-variate functions in $\mathcal{C}[m^{c_0}]$. Now consider the $\mathsf{NE}$ machine that, on input $x$ of length $n$, guesses a string of length $2^n$, runs the compression algorithm for $\mathcal{C}[n^{2c_0}]$ on it, and accepts iff no circuit of size below $2^n/n$ is produced. It accepts every input, since incompressible strings exist at every length, yet every witness it accepts is the truth table of a function needing $\mathcal{C}$-circuits larger than $n^{2c_0}$; read as a prefix of an $m$-variate truth table, it contradicts the easy-witness property. A similar implication was proved independently by Williams.

## Depends on

- [The complexity class NEXP](../../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [Compression of truth tables of small formulas, AC0 circuits and read-once branching programs](compression-of-truth-tables-of-small-circuits.md)

## Proof depends on

- [Impagliazzo–Kabanets–Wigderson easy witness lemma for NEXP](../../../circuit-complexity/algorithmic-method-nqp-and-almost-everywhere-bounds/easy-witness-ikw.md)

## Sources

- Ruiwen Chen, Valentine Kabanets, Antonina Kolokolova, Ronen Shaltiel and David Zuckerman, "Mining Circuit Lower Bound Proofs for Meta-Algorithms", *Computational Complexity* 24, 2015, https://doi.org/10.1007/s00037-015-0100-0 (Theorem 7.1 and Claim 7.2, Section 7).
