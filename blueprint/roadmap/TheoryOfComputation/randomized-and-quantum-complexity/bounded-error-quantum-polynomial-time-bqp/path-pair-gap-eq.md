# Gap and acceptance probability

For a circuit `gs` of well-formed gates (unitary 2-local
gates, `QGateWellFormed`) run on the BQP initial state `bqpInitState x a`, the path-pair gap for
paths from the initial index `bqpInitIndex x a` equals the squared product of the gate
denominators times `2 * acceptProb - 1`.
