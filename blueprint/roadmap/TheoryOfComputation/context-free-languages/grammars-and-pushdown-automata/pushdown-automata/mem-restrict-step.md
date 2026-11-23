# Transitions of the restricted pushdown automaton

Let $M$ be a pushdown
automaton with stack alphabet $\Gamma$, and let $M|_{\Gamma_0}$ be its restriction to a
finite set $\Gamma_0 \subseteq \Gamma$ of stack symbols that contains the initial stack
symbol and is closed for $M$. Let $q, q'$ be states, $o$ an input option (an input
letter, or none for an $\varepsilon$-transition), $\gamma \in \Gamma_0$ and $s$ a list of
symbols of $\Gamma_0$. Then $(q', s)$ is a transition of $M|_{\Gamma_0}$ from $q$ on $o$
with top symbol $\gamma$ if and only if $(q', s)$, with $s$ read as a list of symbols
of $\Gamma$, is a transition of $M$ from $q$ on $o$ with top symbol $\gamma$.
