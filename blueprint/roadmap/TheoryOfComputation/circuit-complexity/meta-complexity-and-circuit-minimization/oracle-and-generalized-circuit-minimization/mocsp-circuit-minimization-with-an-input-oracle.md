# MOCSP: circuit minimization with an oracle truth table in the input

The Minimum Oracle Circuit Size Problem MOCSP takes a truth table $T$, a threshold $s$ and the truth table of an oracle function $O$, and asks whether some circuit with $O$-oracle gates and at most $s$ wires computes $T$. Unlike $\mathrm{MCSP}^A$, the oracle is part of the input.

**Definition (Ilango).** An *oracle circuit* consists of NOT gates, fan-in-two AND and OR gates, and oracle gates $g_1,\dots,g_t$ for some $t\ge0$. Given an oracle function $O$, $C^O(x)$ is the value of $C$ on $x$ when every oracle gate computes $O$. The size $|C|$ of an oracle circuit is its number of wires, and $\mathrm{CC}^O(f)$ is the least size of an $O$-oracle circuit computing $f$. MOCSP takes as input a truth table $T$, a threshold $s\in\mathbb{N}$ and an oracle truth table $O$, and outputs whether $\mathrm{CC}^O(T)\le s$; this output is written $\mathrm{MOCSP}(T,s;O)$.

MOCSP is in NP, and MCSP reduces to it trivially by giving no oracle, so MOCSP is at least as hard as MCSP and serves as a testing ground for hardness results conjectured for MCSP.

## Expansion

A certificate is the oracle circuit itself, whose evaluation on all inputs takes time polynomial in the length of $T$ and $O$. Contrast with $\mathrm{MCSP}^A$, where one oracle $A$ is fixed in advance and may be far more powerful than anything given explicitly: there the oracle changes the problem, while here each instance carries its own small oracle table.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

None.

## Sources

- Rahul Ilango, "Approaching MCSP from Above and Below: Hardness for a Conditional Variant and AC0[p]", *Innovations in Theoretical Computer Science Conference (ITCS)*, 2020, https://doi.org/10.4230/LIPIcs.ITCS.2020.34 (Definition 2.4, Section 1).
