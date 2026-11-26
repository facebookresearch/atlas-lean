# Pushdown automaton

A pushdown automaton over an input alphabet $T$, with
states in $\sigma$ and stack alphabet $\Gamma$, consists of a transition function, a start
state in $\sigma$ and an initial stack symbol in $\Gamma$. The transition function assigns
to each state $q$, each input option (a letter of $T$, or none for an
$\varepsilon$-transition) and each popped stack symbol $\gamma$ a finite set of pairs
$(q', u)$ of a next state $q'$ and a list $u$ of stack symbols to push.

This is the generalized model: the state and stack types themselves are unrestricted,
and only each transition is finitely branching. A standard (textbook) pushdown
automaton is additionally finitely supported; without that, the language it accepts can
be an arbitrary language, so the conversion from pushdown automata back to context-free
grammars needs finiteness hypotheses.
