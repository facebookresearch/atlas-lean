# Blocks

Transform a raw sequence of frames: emit `initial` when a frame starts, apply `bit` to each
payload bit, and apply `close` to the last payload bit (or `none` for an empty payload) at its
terminator. An incomplete trailing frame has no closing output.
