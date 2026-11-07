# Frame emitter takes one step per payload bit plus one

Emit a complete frame in `payload.length + 1` steps, restoring the
input suffix and leaving every unrelated stack unchanged.
