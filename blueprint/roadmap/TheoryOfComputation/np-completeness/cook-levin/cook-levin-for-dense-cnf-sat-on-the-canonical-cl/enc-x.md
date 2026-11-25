# Tableau encoding with a chosen accept symbol

Given a finite multi-stack Turing machine
$M$ and a symbol $a$ of its output-stack alphabet, this is the encoding of $M$ that numbers the
stacks and the pairs (optional label, state) through their finite enumerations, and whose
effective alphabet on each stack $k$ is the set of symbols some statement of $M$ can push on $k$
(plus the whole input alphabet if $k$ is the input stack), with $a$ added if $k$ is the output
stack. A symbol in that set has code one more than its position in it; any other symbol has
code $0$.
