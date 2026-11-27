# Hamiltonian-cycle to TSP converter

The Hamiltonian-cycle to TSP converter takes a Boolean
array $x$ and, starting from the empty array, scans $x$ from left to right and appends the
negation of each cell, charging one time unit before and one time unit after each append (one
read and one write per cell). It returns the resulting array of negated cells together with the
total time charged.
