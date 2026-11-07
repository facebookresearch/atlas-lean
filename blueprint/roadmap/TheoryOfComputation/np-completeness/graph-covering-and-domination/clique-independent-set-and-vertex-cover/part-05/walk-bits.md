# Bits pushed by a walk of the CLIQUE emitter

Let $l = (x, p)$ be a literal occurrence
with name $x \in \mathbb{N}$ and polarity $p$, let $f$ be a Boolean, and let $ds$ be a list whose
items are literal occurrences or clause markers. The bit list $\mathrm{walkBits}(l, f, ds)$ is
defined by recursion on $ds$: it is empty if $ds$ is empty; if $ds$ is a clause marker followed
by $ds'$, it is $\mathrm{walkBits}(l, \mathrm{true}, ds')$; and if $ds$ is an occurrence $l'$
followed by $ds'$, it is the bit $f \wedge \mathrm{adj}(l, l')$ followed by
$\mathrm{walkBits}(l, f, ds')$. Here $\mathrm{adj}(l, l')$ is the Karp adjacency of literals: it
is false exactly when $l$ and $l'$ have the same name and opposite polarities.

The flag $f$ records whether a clause marker has been passed; while it is false, each occurrence
contributes a false bit.
