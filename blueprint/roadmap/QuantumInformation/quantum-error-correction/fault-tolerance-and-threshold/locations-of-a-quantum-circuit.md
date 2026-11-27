# Locations of a quantum circuit

A quantum circuit $C$ is a set of locations $C_i$, each a preparation location (introducing a new qubit), a gate location,
a wait location (a qubit left idle for one time step) or a measurement location (removing a qubit). The circuit is divided
into time steps so that at each time step every qubit then present is involved in exactly one location, the first location
of each qubit is a preparation and the last is a measurement. Two locations are consecutive if they occur at adjacent time
steps and share a qubit. The size $|C|$ is the number of locations. Fault-tolerant protocols replace each location by a
gadget acting on encoded blocks and insert error-correction gadgets between consecutive locations; errors are modelled
as faults at locations.

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 5.1, Definition 6.
