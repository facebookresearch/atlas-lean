# Every finite ε-NFA has an encoding

Let $\alpha$ be a finite alphabet and let $M$ be a nondeterministic finite automaton with
$\varepsilon$-moves over $\alpha$ with a finite set of states. Then there is an encoded NFA $N$ over
$\alpha$ with the same language as $M$. Here an encoded NFA consists of finite lists of natural numbers
for the start states and the accepting states, a finite list of transitions $((s, a), t)$ (on letter
$a$, state $s$ may move to $t$) and a finite list of $\varepsilon$-moves $(s, t)$, all states being
natural numbers; its language is the language of the $\varepsilon$-NFA with state set $\mathbb{N}$ that
these lists describe.
