# Busy Beaver machine

A Busy Beaver machine with $n$ working states is a transition table
that assigns to each of the $n$ working states and each read symbol in $\{0, 1\}$ a symbol in
$\{0, 1\}$ to write, a head movement (left or right), and a next state, which is either one of
the $n$ working states or the halt state.

The write and move of a halting transition are still performed, and the halting step counts
toward the runtime.
