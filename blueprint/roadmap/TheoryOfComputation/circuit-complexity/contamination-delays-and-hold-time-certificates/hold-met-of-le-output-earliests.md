# Hold certificate

A register clocked at time `0` launches the circuit
inputs, which after the edge cannot change before its minimum clock-to-Q delay
`tqMin`. Under the causal gate-delay model, if `hold + u ≤ tqMin + earliest_path`, where
`earliest_path` is the output's earliest change with inputs changing at time
`0`, the receiving register's hold check passes.
