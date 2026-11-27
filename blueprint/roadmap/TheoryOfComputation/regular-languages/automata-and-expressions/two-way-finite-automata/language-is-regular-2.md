# Finite two-way nondeterministic automata accept regular languages

Every
nondeterministic two-way automaton with finitely many states accepts a regular language.

A run of such an automaton on a word starts in a start state with the head at the first
position; each step reads the symbol under the head, changes the state and moves the head one
position left, keeps it in place, or moves it one position right, and the run is stuck if the
head would move left of the first position. A word is accepted when some run ends in an
accepting state with the head just past the last symbol.
