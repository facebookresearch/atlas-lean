# Nerode classes to DFA states

For a language $L$ and a DFA $M$ over the same alphabet,
this map sends each Nerode class $q$ of $L$ to the state that $M$ reaches from its start
state on the chosen representative of $q$.

Unlike the canonical map from words to states, this does not claim that equivalent words reach
equal states in a nonminimal DFA.
