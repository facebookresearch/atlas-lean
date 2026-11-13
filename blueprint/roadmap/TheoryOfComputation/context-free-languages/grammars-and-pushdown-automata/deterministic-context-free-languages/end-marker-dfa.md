# DFA recognizing end-marker encodings

The DFA for the encodings: state `inl false` while reading left
letters, `inl true` after the end marker (the accepting state), and
`inr ()` dead once anything follows the end marker.

## Sources

- Hopcroft, Motwani, and Ullman, Introduction to Automata Theory, Languages, and Computation, 3rd ed., Section 10.3.
