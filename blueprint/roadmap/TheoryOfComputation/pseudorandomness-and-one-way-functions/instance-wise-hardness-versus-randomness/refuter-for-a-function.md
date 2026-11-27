# Refuters for a function against a class of probabilistic algorithms

Let $\mathcal{C}=\bigcup_n\mathcal{C}_n$, where $\mathcal{C}_n$ is a set of probabilistic algorithms on $n$-bit inputs (circuits, RAMs, streaming algorithms of bounded description length), and let $f\colon\{0,1\}^*\to\{0,1\}^*$. An algorithm $A$ is a **refuter for $f$ against $\mathcal{C}$** if for every $n$ and every $C\in\mathcal{C}_n$, $A(1^n,\langle C\rangle)$ outputs $x\in\{0,1\}^n$ with $\Pr[C(x)=f(x)]<2/3$, the probability being over the coins of $C$. It is an **FP-refuter** if it runs in deterministic polynomial time, and a **BPP-refuter** if it runs in probabilistic polynomial time and outputs such an $x$ with probability at least $2/3$.

The class $\mathrm{str}\text{-}\mathrm{TISP}[t(n),s(n)]$ consists of probabilistic one-pass streaming algorithms with description length $n$ that on $n$-bit inputs run in time $t(n)$ and space $s(n)$.

## Depends on

- [Randomized streaming algorithm with $s$ bits of memory](../../../ComputerScience/randomized-algorithms/frequency-moments-of-data-streams/streaming-algorithm.md)

## Sources

- Lijie Chen, Roei Tell and Ryan Williams, "Derandomization vs Refutation: A Unified Framework for Characterizing Derandomization", FOCS (2023), ECCC TR23-105.
