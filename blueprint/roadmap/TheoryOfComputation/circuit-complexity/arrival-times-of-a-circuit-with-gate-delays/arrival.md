# Arrival time of a gate's output

A straight-line circuit program over a gate signature has a fixed number of input wires and a sequence of gates; each gate applies an operation of the signature to a list of wires (inputs or earlier gates), one for each argument position of the operation. Given a real arrival time for every wire and a real delay $d$, the arrival time of a gate's output is

$$d + \max(0, a_1, \dots, a_k),$$

where $a_1, \dots, a_k$ are the arrival times of the wires the gate reads, in argument order; the maximum is taken starting from the time origin $0$. A gate with no inputs therefore arrives at time $d$, and negative input arrival times are replaced by $0$.
