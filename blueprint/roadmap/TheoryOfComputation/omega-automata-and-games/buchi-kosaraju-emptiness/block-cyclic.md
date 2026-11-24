# Block Cyclic

A block is *cyclic* if it contains two distinct states, or one state
with a self-loop in the graph. The distinctness matters: a list such as
`[s, s]` has length `2` but only one state, and is cyclic only if `s` has a
self-loop.
