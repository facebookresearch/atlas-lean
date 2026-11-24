# Acceptance by a single-tape nondeterministic machine is recursively enumerable

Let $m$ be a single-tape nondeterministic Turing machine (in the model of this topic, whose transitions
cannot test for a blank) with a finite set of states and a finite tape alphabet $\Sigma$ that has
decidable equality and a primitive recursive encoding. The set of words over $\Sigma$ that $m$
accepts is recursively enumerable.

A word is accepted exactly when some list of transition labels applies to its input tape without a
failed read and leads from a start state to an accepting state. Both conditions are computable
from the word and the list: the tape is coded by lists, and the set of states reachable along a
list is a finite set computed by iterating the image of the start states. Searching over the
lists enumerates the accepted words.

## Sources

- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage Learning, 2013,
  Theorem 3.16 (here through recursion theory rather than a breadth-first simulation).
