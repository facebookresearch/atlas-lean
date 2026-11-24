# Sumcheck1 sound

Soundness: if `p` has degree at most `d` and the claim is false
(`H ≠ p.eval 0 + p.eval 1`), then every prover message `q` is accepted at no more than `d`
challenges. A message failing the degree or Boolean-sum check is accepted nowhere; one
passing both differs from `p`, so `card_agree_le` applies.
