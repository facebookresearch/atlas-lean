# Accept1

One-variable Boolean sum-check verifier with degree bound `d`: for the claim
"`p.eval 0 + p.eval 1 = H`", it accepts the prover's polynomial `q` at challenge `r` when
`q` has degree at most `d`, the Boolean sum of `q` is `H`, and `q` agrees with the oracle
`p` at `r`.
