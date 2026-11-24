# Split Preorder C

Assume that `V` carries a Boolean equality test `==`.

Costed split: the same blocks as `splitPreorder`, plus the cost. The
cost counts one hash-table insertion per root for the `Std.HashSet.ofList`
construction plus the accumulator's tests (`splitPreorder.goC`).
