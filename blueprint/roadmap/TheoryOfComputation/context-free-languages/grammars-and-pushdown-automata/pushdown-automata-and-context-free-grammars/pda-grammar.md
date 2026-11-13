# Triple grammar of a pushdown automaton

Let $M$ be a pushdown automaton over the alphabet
$T$ with a finite set $\sigma$ of states, a finite stack alphabet $\Gamma$, start state $q_0$
and initial stack symbol $Z_0$, and let $T_0$ be a finite set of letters. The triple grammar of
$M$ and $T_0$ is the context-free grammar over $T$ whose nonterminals are an initial
nonterminal $S$ and the triples $(p, \gamma, q)$ with $p, q \in \sigma$ and $\gamma \in \Gamma$.
Its productions are the start productions $S \to (q_0, Z_0, q)$ for every state $q$, and the
transition productions: for every state $p$, stack symbol $\gamma$, input $a$ that is
$\varepsilon$ or a letter of $T_0$, transition of $M$ from $p$ on $a$ popping $\gamma$ that
moves to a state $r$ and pushes $\gamma_1 \cdots \gamma_k$, and all states $s_1, \dots, s_k$,
writing $s_0 = r$, the production

$$(p, \gamma, s_k) \to a\,(s_0, \gamma_1, s_1)(s_1, \gamma_2, s_2) \cdots (s_{k-1}, \gamma_k, s_k)$$

where $a$ is omitted when it is $\varepsilon$ (for $k = 0$ this is $(p, \gamma, r) \to a$).

The nonterminal $(p, \gamma, q)$ is meant to derive the words that take $M$ from state $p$ with
stack $\gamma$ to state $q$ with empty stack; transitions on letters outside $T_0$ are not
used.
