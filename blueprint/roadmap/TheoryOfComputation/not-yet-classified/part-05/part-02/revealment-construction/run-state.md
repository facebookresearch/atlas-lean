# Run State

Run a guard/step state machine on a configuration in a single pass over the
supplied list. This does not in general reach a fixpoint: a second pass can add
more, for example on a path `0 — 1 — 2` starting from `{2}` and scanning the open
edges in order `[0 — 1, 1 — 2]`.
