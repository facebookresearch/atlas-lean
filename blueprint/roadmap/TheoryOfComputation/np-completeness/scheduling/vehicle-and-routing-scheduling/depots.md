# Depots of a multiple-depot vehicle scheduling instance

The depots of a MULTIPLE-DEPOT VEHICLE SCHEDULING instance are the listed triples, returned unchanged: each triple consists of a depot's vehicle count $r_d$, a list of pull-out costs and a list of pull-in costs. The lists are arbitrary on raw input: for an instance with one trip the triple $(1, [\,], [7, 8])$ stays as it is. On well-formed instances each list has exactly one entry per trip, $[o_{d0}, \dots, o_{d(n-1)}]$ for the pull-out costs to the trips and $[e_{0d}, \dots, e_{(n-1)d}]$ for the pull-in costs from the trips.
