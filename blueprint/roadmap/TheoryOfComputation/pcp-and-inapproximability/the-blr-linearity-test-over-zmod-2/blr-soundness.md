# Blr soundness

Blum–Luby–Rubinfeld soundness: let `f : (ZMod 2)ⁿ → ZMod 2` and `ε ≥ 0`. If `f` passes the linearity test (checking `f x + f y = f (x + y)` for uniformly random `x, y`) with probability at least `1 - ε`, then there is `a ∈ (ZMod 2)ⁿ` such that `f` disagrees with the linear function `x ↦ a · x` on at most an `ε` fraction of inputs.
