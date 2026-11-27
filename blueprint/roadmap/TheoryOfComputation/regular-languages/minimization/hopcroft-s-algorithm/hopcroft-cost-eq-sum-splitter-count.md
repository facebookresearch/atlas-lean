# Hopcroft predecessor-work as splitter counts plus pops

Let $M$ be a deterministic finite automaton with a finite input alphabet $\Sigma$, listed in a fixed order, a finite state set $Q$ with $n = |Q|$, transition function $\delta$ and accepting set $F$. For $C \subseteq Q$ and $a \in \Sigma$, $\mathrm{pre}(C, a) = \{q \in Q : \delta(q, a) \in C\}$; a set $X$ splits a block $D$ if $D \cap X$ and $D \setminus X$ are both nonempty; and $\mathrm{sm}(A, B)$ is $A$ if $|A| \le |B|$ and $B$ otherwise. The predecessor cost of a list of splitters is $\sum_{(C, a)} (|\mathrm{pre}(C, a)| + 1)$ over its entries: one unit per predecessor visit and one per popped splitter. For $q \in Q$, $b \in \Sigma$ and a list $W$ of splitters, the splitter count $\mathrm{cnt}(q, b, W)$ is the number of entries $(C, b')$ of $W$, counted with multiplicity, with $b' = b$ and $q \in C$. For every finite list $t$ of splitters,

$$\mathrm{cost}(t) = \sum_{b \in \Sigma} \sum_{q \in Q} \mathrm{cnt}(\delta(q, b), b, t) + |t|.$$

Every incoming transition is counted, even when many states have the same successor.
