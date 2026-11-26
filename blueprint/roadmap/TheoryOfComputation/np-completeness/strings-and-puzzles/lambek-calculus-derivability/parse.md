# Parse

Read a postfix token list onto a stack of types: `0`, `1`, `2` pop `Y` and `X` and push `X · Y`,
`X / Y` and `X \ Y`, and `k + 3` pushes `pₖ`. The result is the single type left on the stack,
or `none` when a token lacks its operands or the final stack does not contain exactly one type
(for example, empty input and an empty initial stack).
