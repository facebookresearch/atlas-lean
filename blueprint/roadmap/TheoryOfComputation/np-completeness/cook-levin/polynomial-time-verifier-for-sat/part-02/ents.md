# Occurrence table of a formula and a witness

Let $\varphi$ be a CNF formula, $w$ a list
of booleans, and $n_0, \dots, n_{k-1}$ the variable indices of the literals of $\varphi$ in
reading order, with repetitions. The occurrence table is the list of $k$ entries whose $i$-th
entry pairs the binary name of $n_i$ (its canonical binary representation, least significant
bit first, empty for $0$) with the value $w_i$ if $i$ is less than the length of $w$, and with
no value otherwise.
