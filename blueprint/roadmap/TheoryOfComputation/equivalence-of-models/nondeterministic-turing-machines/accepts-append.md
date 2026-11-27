# Acceptance is closed under extension on the right

Let $m$ be a single-tape nondeterministic Turing machine (in the model of this topic, whose transitions
cannot test for a blank). If $m$ accepts a word $x$ over its tape alphabet, then $m$
accepts $xy$ for every word $y$ over that alphabet.

A transition can test the cell under the head only for a symbol, never for a blank, so every cell
that an accepting run on $x$ reads holds a letter of $x$ or a symbol that the run wrote there
earlier. On the input $xy$ these cells hold the same symbols, and the same run accepts $xy$. For
machines that can test for blank cells the statement fails.

## Sources

- defect of the pinned CSLib definition, fixed upstream by leanprover/cslib#1039.
