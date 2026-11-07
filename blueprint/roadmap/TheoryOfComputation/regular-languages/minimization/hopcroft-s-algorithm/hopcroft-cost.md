# Predecessor cost of a Hopcroft splitter trace

The predecessor cost of a splitter trace: for each popped splitter `(C, a)`, one
predecessor visit per state in the preimage `preimage M C a`, plus `1` per-splitter
overhead. This is the quantity the total-work bound, not proved here, constrains
to `O(|Σ| n log n)`. Charging splitter size `C.card` instead
would undercount: if all `n` states transition on `a` to one state `q`, processing the
singleton splitter `({q}, a)` costs `n` predecessor visits while `C.card` charges
only `1`.
