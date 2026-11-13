# Effect of one splitter on the common-block relation

Let $M$ be a DFA with transition
function $\delta$, $P$ a list of blocks of states, $C$ a set of states and $a$ a letter. Two states
$p$ and $q$ lie in a common block after the splitter $(C, a)$ is applied to $P$ if and only if
they lie in a common block of $P$ and $\delta(p, a) \in C \iff \delta(q, a) \in C$.
