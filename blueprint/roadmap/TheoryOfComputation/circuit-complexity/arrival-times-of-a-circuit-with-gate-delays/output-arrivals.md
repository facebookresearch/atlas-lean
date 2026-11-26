# Arrival times of a circuit's outputs

A straight-line circuit program over a gate signature has a fixed number of input wires and a sequence of gates; each gate applies an operation of the signature to a list of wires (inputs or earlier gates), one for each argument position of the operation. A circuit is such a program with a list of designated output wires. Given a real delay for every gate and a real arrival time for every input, the arrival time of each designated output is the arrival time of the wire it designates: an input wire at its given time, a gate at its computed arrival time.
