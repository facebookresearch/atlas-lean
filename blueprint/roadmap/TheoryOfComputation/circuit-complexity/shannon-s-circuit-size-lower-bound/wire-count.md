# Wire count of a flat circuit

The wire count of a flat Boolean circuit on $n$ inputs,
given as a list of gates, is the sum over its gates of the lengths of their predecessor lists:
every reference of a gate to a gate index is counted, with multiplicity, while input variables
and constants contribute nothing and the modulus of a mod gate is not counted.
