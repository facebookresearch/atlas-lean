# Gate description in a succinct circuit (Succinct Circuit Value)

Let $C$ be a list of
encoded gates and let $n, i \in \mathbb{N}$. Decode each gate of $C$ into a gate of a flat
Boolean circuit on $n$ inputs and evaluate it with input $j < n$ set to bit $j$ of $i$, least
significant bit first, that is, true exactly when $\lfloor i / 2^j \rfloor$ is odd. The
description of gate $i$ of the circuit succinctly described by $C$ is the list of the last
$2n + 3$ resulting gate values, or of all of them if $C$ has fewer than $2n + 3$ gates.
