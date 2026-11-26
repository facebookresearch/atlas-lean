# A gate arrives no earlier than each of its inputs plus its delay

A straight-line circuit program over a gate signature has a fixed number of input wires and a sequence of gates; each gate applies an operation of the signature to a list of wires (inputs or earlier gates), one for each argument position of the operation. Fix real arrival times for all wires and a real delay $d$ for a gate. For every argument position $j$ of the gate, $d$ plus the arrival time of the wire read at position $j$ is at most the arrival time of the gate's output.
