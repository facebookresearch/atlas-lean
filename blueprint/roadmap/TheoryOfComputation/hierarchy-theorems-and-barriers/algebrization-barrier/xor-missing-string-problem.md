# XOR-Missing-String problem

In XOR-Missing-String, Alice and Bob each hold $m<2^{n/2}$ strings of length $n$ and must output an $n$-bit string that differs from every XOR $x_i\oplus y_j$. Communication lower bounds for it translate into algebrization barriers for circuit lower bounds.

**Missing-String.** For $m<2^n$, given query access to a list $x_1,\dots,x_m\in\{0,1\}^n$, output a string in $\{0,1\}^n$ not in the list. Decision-tree upper bounds for Missing-String yield relativizing circuit lower bounds, and decision-tree lower bounds yield relativized worlds with small circuits; relativizing algorithms for range avoidance are equivalent to decision trees for Missing-String.

**XOR-Missing-String$(n,m)$.** Let $m<2^{n/2}$. Alice receives $x_1,\dots,x_m\in\{0,1\}^n$ and Bob receives $y_1,\dots,y_m\in\{0,1\}^n$. They communicate and output $s\in\{0,1\}^n$ with

$$
s\ne x_i\oplus y_j\quad\text{for all }1\le i,j\le m,
$$

where $\oplus$ is bitwise XOR. Since $m^2<2^n$, a solution always exists.

Basic facts:

1. The two-party version of plain Missing-String is easy: with $m\le 2^n/10$, binary search on the counts $|\{i:x_i\le s\}|+|\{i:y_i\le s\}|$ finds a missing string with $O(n\log m)$ bits of deterministic communication.
2. Outputting a uniformly random $n$-bit string solves XOR-Missing-String with $O(n)$ communication and error $m^2/2^n$, but this protocol is not pseudodeterministic.
3. By the transfer principle, an algorithm with oracle access to the multilinear extension $\tilde A$ of an oracle $A$ can be simulated by a communication protocol in which Alice holds the half of $A$ with first bit $0$ and Bob the half with first bit $1$, so communication lower bounds for XOR-Missing-String give oracles $A$ relative to which $\tilde A$-machines fail to find hard truth tables.

## Expansion

The XOR form is what defeats binary search: the forbidden set $\{x_i\oplus y_j\}$ is spread across all of $\{0,1\}^n$ and no player can count its elements below a threshold locally. Lower bounds hold against $\mathsf{PostBPP}$ protocols with error at most $2^{-5n}$ (which need $\Omega(m)$ communication when $20n\le m<2^{n/2}$), against several pseudodeterministic $\mathsf{BPP}$ protocols that may perform win-win analyses on each other's inputs, and against robust $\mathsf{FMA}$ protocols of complexity $C$, which solve at most a $2^{-\Omega(m/C)+O(C+n)}$ fraction of inputs.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](../../complexity-classes/tfnp-hierarchies-and-avoidance/range-avoidance-and-explicit-constructions/range-avoidance-problem.md)
- [Multilinear extension of a Boolean function](multilinear-ext.md)

## Proof depends on

None.

## Sources

- Lijie Chen, Yang Hu and Hanlin Ren, "New Algebrization Barriers to Circuit Lower Bounds via Communication Complexity of Missing-String", *Innovations in Theoretical Computer Science (ITCS)*, 2026, arXiv:2511.14038v1 (Problems 1.1 and 1.2, Theorem 1.4, Theorem 1.6, Lemma 1.8, Theorem 2.6, Section 1).
