# Multistack pushdown automata

A **multistack pushdown automaton** (MPDA) with $n$ stacks over an input alphabet $\Sigma$ has a finite set of control states, a stack alphabet $\Gamma$, initial and final states, and transitions of three kinds: $q\xrightarrow{a,\ \mathrm{nop}}q'$, $q\xrightarrow{a,\ \mathrm{push}_s(\gamma)}q'$ and $q\xrightarrow{a,\ \mathrm{pop}_s(\gamma)}q'$ for a stack $s\in[n]$, $\gamma\in\Gamma$ and $a\in\Sigma\cup\{\varepsilon\}$. A configuration is a control state with $n$ stack contents; a run is accepting if it goes from an initial state with all stacks empty to a final state with all stacks empty. In a **visibly** MPDA the input letter determines the kind of the transition and its stack. Reachability (and emptiness) for MPDA with $n\ge2$ stacks is undecidable, since two stacks simulate a Turing tape.

## Depends on

- [Pushdown automaton](../pushdown-automata/pda.md)
- [Language accepted by a pushdown automaton](../pushdown-automata/accepts.md)

## Proof depends on

- [Multi-stack machines and multi-tape Turing machines simulate each other in polynomial time and space](../../../equivalence-of-models/ram-word-ram-and-pointer-machines/multistack-multitape-equivalence.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), arXiv:2002.05950, 2020.
