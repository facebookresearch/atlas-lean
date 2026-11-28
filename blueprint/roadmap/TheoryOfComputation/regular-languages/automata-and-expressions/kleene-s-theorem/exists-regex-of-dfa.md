# Kleene's theorem: DFA languages are regex-denoted

Let $\alpha$ be a finite alphabet and $M$ a deterministic automaton over $\alpha$ with a finite set of states. Then
there is a regular expression over $\alpha$ whose language is the language accepted by $M$. The same holds for a deterministic automaton given in the general automata framework (with a transition function, a start state and an accepting set): converting it to a DFA keeps its states, transitions, start state, accepting set and language.
