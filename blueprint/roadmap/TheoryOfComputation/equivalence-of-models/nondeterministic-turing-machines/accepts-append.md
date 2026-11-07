# Acceptance is closed under extension on the right

If a single-tape nondeterministic
Turing machine $m$ accepts a word $x$ over its tape alphabet, then $m$ accepts $xy$ for every word
$y$ over that alphabet.

This is a defect of CSLib's definition of these machines: a transition can only test the cell
under the head for a symbol, never for a blank, so every cell that an accepting run on $x$ reads
holds a letter of $x$ or one the run wrote, and the same run accepts $xy$.

## Sources

- defect of the pinned CSLib definition, fixed upstream by leanprover/cslib#1039.
