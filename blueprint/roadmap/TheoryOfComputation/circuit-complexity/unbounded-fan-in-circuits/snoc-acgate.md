# Snoc ACGate

Append one flat gate `g` to a CSLib circuit whose `k` outputs carry the first `k` gates of a
flat circuit, given that `g` references only those gates (`h`). A `var i` gate adds no CSLib
gate: its output is the input wire `i`. Every other gate adds one CSLib gate, which reads the
outputs named by its references and becomes the new last output.
