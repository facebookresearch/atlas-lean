# Multistack pushdown automata

A **multistack pushdown automaton** (MPDA) is a tuple $M=(S,\Delta,s_0,S_f,n,\Sigma,\Gamma)$ where $S$ is a finite non-empty set of locations (control states), $\Delta$ is a finite set of transitions, $s_0\in S$ is the initial location, $S_f\subseteq S$ is a set of final locations, $n\in\mathbb{N}$ is the number of stacks, $\Sigma$ is a finite input alphabet and $\Gamma$ is a finite stack alphabet containing a bottom symbol $\bot$. A transition is a tuple $(s,\mathrm{op},a,s')$ with source $s$, target $s'$, label $a\in\Sigma$ and operation $\mathrm{op}$ one of $\mathrm{nop}$ (no stack operation), $\mathrm{push}_i(\alpha)$, pushing $\alpha\in\Gamma$ onto stack $i\in\{1,\dots,n\}$, or $\mathrm{pop}_i(\alpha)$, popping stack $i$ if its top is $\alpha$. A configuration is a tuple $(s,\lambda_1,\dots,\lambda_n)$ of a current location and the contents $\lambda_i\in\Gamma^*$ of the stacks; a run is accepting if it starts from the initial location and reaches a final location with all stacks empty, and the language of $M$ is the set of words labelling accepting runs. Reachability for MPDA is undecidable in general.

## Proof sketch

Derived here (not stated in the cited source): reachability, and hence emptiness, is already undecidable for $n\ge2$ stacks, by the simulation of multi-tape Turing machines by multi-stack machines, as two stacks hold the tape contents to the left and to the right of the head.

## Depends on

- [Pushdown automaton](../pushdown-automata/pda.md)
- [Language accepted by a pushdown automaton](../pushdown-automata/accepts.md)

## Proof depends on

- [Multi-stack machines and multi-tape Turing machines simulate each other in polynomial time and space](../../../equivalence-of-models/ram-word-ram-and-pointer-machines/multistack-multitape-equivalence.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), Lecture Notes in Computer Science 12078, 2020, Section 1, first sentence (undecidability), and Section 2 (the definition of an MPDA); arXiv:2002.05950.
