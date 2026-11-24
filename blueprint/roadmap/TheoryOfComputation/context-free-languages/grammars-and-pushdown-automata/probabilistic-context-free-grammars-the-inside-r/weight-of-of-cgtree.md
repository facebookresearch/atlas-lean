# Weight Of of CGTree

`ofCGTree` turns the one-nonterminal weight into the derivation weight: under rule
weights giving `p` to `A -> A A` and `q` to `A -> a`, the weight of `ofCGTree t` is
`t.weight p q`.
