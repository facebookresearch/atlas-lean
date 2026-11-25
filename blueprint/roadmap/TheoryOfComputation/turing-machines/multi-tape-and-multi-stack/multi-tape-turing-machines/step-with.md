# Successor under a transition function

Let $\delta$ be a transition function of a
multi-tape Turing machine with $k$ work tapes, assigning an action to each state, input symbol
and tuple of $k$ work tape symbols, where a symbol may be blank. The successor of a configuration
$c$ under $\delta$ is $c$ itself if $c$ is halted, and otherwise the configuration obtained by
applying to $c$ the action $\delta(q, a, b)$, where $q$ is the state of $c$, $a$ the symbol under
its input head and $b$ the symbols under its work tape heads.
