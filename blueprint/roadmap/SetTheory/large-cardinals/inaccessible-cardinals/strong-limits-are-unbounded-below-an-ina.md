# Strong limits are unbounded below an inaccessible cardinal

Strong limits are unbounded below an inaccessible `κ`: above any `a < κ` sits
`ℶ_{a.ord + ω}`, a strong limit by `isStrongLimit_beth` since `a.ord + ω` is a
limit ordinal (`isSuccLimit_add`), and below `κ` since
`(a.ord + ω).card = a.ord.card + ℵ₀ < κ` (`add_lt_of_lt`).

## Sources

- Above any a < κ with κ inaccessible sits a strong limit cardinal below κ.
