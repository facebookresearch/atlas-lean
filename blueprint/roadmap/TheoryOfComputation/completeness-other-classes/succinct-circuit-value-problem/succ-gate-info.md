# Decoded gate description (Succinct Circuit Value)

Let $C$ be a list of encoded gates,
let $n, i \in \mathbb{N}$, and let $d$ be the description of gate $i$ of the circuit succinctly
described by $C$: decode each gate of $C$ into a gate of a flat Boolean circuit on $n$ inputs,
evaluate the decoded circuit with input $j < n$ set to bit $j$ of $i$ (true exactly when
$\lfloor i / 2^j \rfloor$ is odd), and take the last $2n + 3$ gate values, or all of them if $C$
has fewer than $2n + 3$ gates. Read a list of booleans $(b_0, \dots, b_{m-1})$ as the number
$\sum_{k < m} [b_k] \, 2^k$, where $[b_k]$ is $1$ if $b_k$ is true and $0$ otherwise, so the
empty list reads as $0$. The information of gate $i$ is the triple $(t, p_1, p_2)$, where the
gate type $t$ is the number read from the first three entries of $d$, the first predecessor $p_1$
is the number read from the next $n$ entries, and the second predecessor $p_2$ is the number read
from all remaining entries; when $d$ is too short, each part uses only the entries that exist.
