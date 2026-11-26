# Reach In

Bounded reachability by midpoint recursion: `reachIn R k x y` decides whether `y` is
reachable from `x` in at most `2 ^ k` steps of `R`. At level `k + 1` it accepts iff some midpoint
`z` is reachable from `x`, and reaches `y`, within `2 ^ k` steps each; the midpoint search is
the existential scan given by `Decidable (∃ z, _)` on the finite type `C`. This is an
extensional decision procedure; no space bound is claimed.
