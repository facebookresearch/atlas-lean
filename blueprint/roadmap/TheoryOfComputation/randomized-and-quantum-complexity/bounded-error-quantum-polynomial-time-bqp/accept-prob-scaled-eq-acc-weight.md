# Explicit scaled acceptance

For a circuit `gs` of well-formed gates (unitary 2-local
gates, `QGateWellFormed`) run on the BQP initial state `bqpInitState x a`, the squared product of
the gate denominators times the acceptance probability equals the accepting cleared weight
`accWeight` for paths from the initial index `bqpInitIndex x a`. This is the explicit form of
`acceptProb_scaled_nat`.
