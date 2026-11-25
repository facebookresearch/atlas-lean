# Direct limit of a directed system

Let `(M i)` be a directed system of types indexed by a preorder `ι`, with
transition maps `f i j : M i → M j` for `i ≤ j`, and let `g i : M i → P` be
maps to a type `P`. The system has direct limit `P` via the maps `g` when
three conditions hold: every element of `P` equals `g i m` for some `i` and
some `m ∈ M i`; whenever `g i mᵢ = g j mⱼ`, there is `k` with `i ≤ k` and `j
≤ k` such that `f i k mᵢ = f j k mⱼ`; and `g j (f i j x) = g i x` for all `i
≤ j` and `x ∈ M i`.
