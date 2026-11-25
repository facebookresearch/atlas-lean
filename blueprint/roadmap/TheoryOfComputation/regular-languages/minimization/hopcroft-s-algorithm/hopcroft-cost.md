# Predecessor cost of a Hopcroft splitter trace

Let $M$ be a deterministic finite automaton with a finite input alphabet $\Sigma$, listed in a fixed order, a finite state set $Q$ with $n = |Q|$, transition function $\delta$ and accepting set $F$. For $C \subseteq Q$ and $a \in \Sigma$, $\mathrm{pre}(C, a) = \{q \in Q : \delta(q, a) \in C\}$; a set $X$ splits a block $D$ if $D \cap X$ and $D \setminus X$ are both nonempty; and $\mathrm{sm}(A, B)$ is $A$ if $|A| \le |B|$ and $B$ otherwise. For a list of splitters $(C_1, a_1), \dots, (C_m, a_m)$, the predecessor cost is

$$\sum_{i=1}^{m} \bigl(|\mathrm{pre}(C_i, a_i)| + 1\bigr):$$

for each popped splitter, one visit per state whose successor lies in $C_i$, plus one unit of overhead.

Charging $|C_i|$ instead would undercount: if all $n$ states go to one state $q$ on $a$, the splitter $(\{q\}, a)$
has $n$ predecessors but size $1$.
