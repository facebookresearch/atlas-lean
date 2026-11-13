# Converter turns a unary count into a canonical binary frame

Emit one canonical Nat frame above any earlier output and restore
all conversion scratch. The old counter is consumed; unrelated stacks,
including `X`, are preserved. Cleanup is part of the charged run.
