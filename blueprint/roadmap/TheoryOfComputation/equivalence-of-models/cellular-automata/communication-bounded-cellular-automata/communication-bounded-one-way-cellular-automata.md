# Communication-bounded one-way cellular automata

A one-way cellular automaton is a line of finite-state cells, one per input letter, in which information flows only leftwards; it is communication bounded when the number of messages sent across each link, or across all links, is bounded by a function of the input length.

A *cellular automaton* $\langle S,F,A,B,\#,b_l,b_r,\delta\rangle$ has a finite set $S$ of cell states, accepting states $F\subseteq S$, input symbols $A\subseteq S$, communication symbols $B$, a boundary symbol $\#\notin B$, communication functions $b_l,b_r:S\to B\cup\{\bot\}$ giving the message sent to the left and right neighbor ($\bot$ meaning no message), and a local transition function $\delta:(B\cup\{\#,\bot\})\times S\times(B\cup\{\#,\bot\})\to S$. On input $w=a_1\cdots a_n$ the cells $1,\dots,n$ start in states $a_1,\dots,a_n$; each step every cell updates from its state and the messages of its neighbors, and the two outer cells receive $\#$ once, at the first step. The input is accepted if the leftmost cell enters an accepting state at some time; the automaton works in *real time* if every accepted $w$ is accepted within $|w|$ steps. It is *one-way* (an OCA) if $b_r$ is constantly $\bot$ and the leftmost cell receives no boundary symbol, so information moves only from right to left.

A *communication* between cells $i$ and $i+1$ at step $j$ happens when $b_r(c_j(i))\neq\bot$ or $b_l(c_j(i+1))\neq\bot$. For an accepting computation on $w$ let $\mathrm{mcomm}(w)$ be the largest number of communications on a single link and $\mathrm{scomm}(w)$ the total over all links. An automaton is *max communication bounded by $f$* (respectively *sum communication bounded*) if every accepted $w$ is accepted by a computation with $\mathrm{mcomm}(w)\le f(|w|)$ (respectively $\mathrm{scomm}(w)\le f(|w|)$); $\mathrm{MC}(f)$-OCA and $\mathrm{SC}(f)$-OCA denote the classes bounded by some $g\in O(f)$. A language is *bounded* if it is included in $a_1^*a_2^*\cdots a_k^*$ for distinct letters $a_1,\dots,a_k$.

## Depends on

None.

## Proof depends on

None.

## Expansion

General real-time one-way cellular automata accept only regular unary languages, but even OCA in which each two neighboring cells communicate only a constant number of times accept non-semilinear bounded languages (Examples 2 and 3 of the source), which is why decision problems for bounded languages can become undecidable.

## Sources

- Martin Kutrib and Andreas Malcher, "Bounded Languages Meet Cellular Automata with Sparse Communication", in *Proceedings of the Eleventh International Workshop on Descriptional Complexity of Formal Systems (DCFS 2009)*, Electronic Proceedings in Theoretical Computer Science 3, 2009, pp. 163–172, doi:[10.4204/EPTCS.3.15](https://doi.org/10.4204/EPTCS.3.15); read in arXiv:0907.5128v1 ([arXiv](https://arxiv.org/abs/0907.5128v1)), whose numbering is used: Definition 1 and the definitions of Section 2 (configurations, acceptance, one-way automata, communication bounds, bounded languages); Section 3 with Examples 2 and 3.
