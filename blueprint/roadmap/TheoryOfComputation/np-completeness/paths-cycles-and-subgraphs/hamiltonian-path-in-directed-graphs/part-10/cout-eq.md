# Outcome of a HAMPATH-verifier equality comparison

Write $\mathrm{cout}(i, o)$ for the
label that counter comparison $i$ of the HAMPATH verifier picks on the ordering
$o \in \{\mathrm{lt}, \mathrm{eq}, \mathrm{gt}\}$. Let $i$ be a counter comparison and $l$ a label
such that $\mathrm{cout}(i, \mathrm{eq}) = l$ and $\mathrm{cout}(i, o)$ is the reject label
$\mathrm{no}$ for every ordering $o \ne \mathrm{eq}$. Then for all $m, n \in \mathbb{N}$, the label
$\mathrm{cout}(i, \mathrm{compare}(m, n))$ on the ordering of $m$ and $n$ is $l$ if $m = n$ and
$\mathrm{no}$ otherwise.
