# Linear μ-calculus model checking as a decision problem

Model checking of the linear μ-calculus as a decision problem over bitstrings:
the input decodes to `(n, edges, worldVals, start, tokens)`, where `worldVals`
lists, per world, the atoms true at that world; the answer is whether the
decoded formula is closed, the structure is well-formed and total (every world
has a successor world, so the path quantification is not vacuous at deadlocks),
and every path from `start` satisfies the formula.
