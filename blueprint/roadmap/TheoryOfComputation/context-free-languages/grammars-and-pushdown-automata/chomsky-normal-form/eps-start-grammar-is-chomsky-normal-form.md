# Adding a fresh start symbol preserves Chomsky normal form

If a context-free grammar
$g$ is in Chomsky normal form and no production of $g$ has empty output, then the fresh-start
grammar of $g$ is in Chomsky normal form.

The no-empty-outputs hypothesis is essential: an existing empty production would be embedded
with the old initial nonterminal, not the fresh one, on the left.
