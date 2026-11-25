# SUDOKU as a decision problem

The decision problem SUDOKU accepts a bitstring $x$ exactly
when $x$ decodes, under the canonical bitstring encoding of pairs of a natural number and a finite
list of finite lists of natural numbers, to a Sudoku instance that is well formed and feasible.
It rejects every bitstring that does not decode to an instance.
