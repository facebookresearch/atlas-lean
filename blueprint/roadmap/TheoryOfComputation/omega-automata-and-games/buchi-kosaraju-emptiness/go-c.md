# Go C

Assume that `V` carries a Boolean equality test `==` and a hash function.

Costed split accumulator: the same walk as `splitPreorder.go`, returning
`(blocks, cost)` where `cost` counts the Boolean tests the walk performs,
with short-circuit accounting: each step charges `1` for the
`rootsSet.contains` test, plus `1` more for the `cur.isEmpty` test only
when `contains` is true (short-circuit `&&`); the empty-input case charges
`1` for the final `cur.isEmpty` test. The cost is produced by the same
recursive evaluation that produces the blocks, not by a separate formula.
