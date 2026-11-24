# Inside stable

Assume that equality on `T` is decidable and that equality on `g.NT` is decidable.

The inside recurrence stabilizes once `d >= |w|`: depth `|w|` already
sums the weights of every valid `PDerivTree` for `w`. Only terminal rules
`A -> a` and binary rules `A -> B C` have trees; rules of other shapes add
nothing to `inside`.
