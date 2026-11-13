# Framed block reader fails on truncated framing

Truncated framing reaches the failure branch within input length
plus one, without assuming that the input is an encoder image. The
destination may contain a partial payload on failure; the caller must
discard or clear it before using that stack again.
