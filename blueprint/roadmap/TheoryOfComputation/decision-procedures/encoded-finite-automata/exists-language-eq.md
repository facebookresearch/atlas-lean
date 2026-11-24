# Every finite DFA has an encoding

Let $\alpha$ be a finite alphabet and let $M$ be a deterministic finite automaton over $\alpha$ with a
finite set of states. Then there is an encoded DFA $D$ over $\alpha$ with the same language as $M$. Here
an encoded DFA consists of a start state $s_0 \in \mathbb{N}$, a finite list of accepting states in
$\mathbb{N}$, and a finite list of transitions $((s, a), t)$; it denotes the DFA with state set
$\mathbb{N}$ whose transition from $s$ on $a$ goes to the target of the first listed transition for
$(s, a)$, and stays at $s$ if there is none.
