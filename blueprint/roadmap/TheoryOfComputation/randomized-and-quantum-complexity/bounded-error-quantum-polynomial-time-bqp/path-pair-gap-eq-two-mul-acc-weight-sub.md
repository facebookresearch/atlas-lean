# Integer gap identity

For a circuit `gs` of well-formed gates (unitary 2-local gates,
`QGateWellFormed`) run on the BQP initial state `bqpInitState x a`, the path-pair gap for paths
from the initial index `bqpInitIndex x a` equals twice the accepting cleared weight minus the
squared product of the gate denominators. By unitarity, that square is the total cleared
weight.
