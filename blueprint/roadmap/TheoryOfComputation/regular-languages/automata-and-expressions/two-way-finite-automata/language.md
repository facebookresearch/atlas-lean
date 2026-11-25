# Language of a deterministic two-way automaton

The language of a deterministic two-way
automaton $A$ is the set of words accepted by $A$ viewed as a nondeterministic two-way
automaton: a word $w$ belongs to it when, starting in the start state with the head at the
first position of $w$ and following the step function of $A$ (which moves the head one
position left, keeps it in place, or moves it one position right, and gets stuck when it is
undefined or would move the head left of the first position), the automaton reaches an
accepting state with the head just past the last symbol of $w$.
