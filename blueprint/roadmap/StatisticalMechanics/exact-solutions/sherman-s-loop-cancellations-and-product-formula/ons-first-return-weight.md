# Weight of a first-return segment avoiding a state

For a set $E$, a matrix $\Lambda \in \mathbb{C}^{E \times E}$, $e, r \in E$ and a list $s$, the weight is $w_\Lambda(s)$ if $s$ is a first-return segment at $e$ none of whose entries equals $r$, and $0$ otherwise; here a first-return segment at $e$ is a list $(e, y_1, \dots, y_k, e)$ with all $y_i \ne e$ and $w_\Lambda(s) = \prod_{i} \Lambda(s_i, s_{i+1})$ is the [edge weight](ons-edge-weight.md) of a list $s$ (the product over consecutive pairs, $1$ for lists of length at most $1$).
