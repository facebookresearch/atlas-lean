# Occurrence table of a list of variables

Given natural numbers $n_0, \dots, n_{k-1}$ and a
list $w$ of bits, the occurrence table is the list of $k$ table entries whose $i$-th entry has as
name the binary code of $n_i$ (binary digits, least significant first, no trailing zero) and as value
the bit $w_i$ if $i$ is less than the length of $w$, and no value otherwise.
