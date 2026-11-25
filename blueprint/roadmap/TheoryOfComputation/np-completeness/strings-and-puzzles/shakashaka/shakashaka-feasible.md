# Feasible instances of SHAKASHAKA

An instance of SHAKASHAKA is feasible when the instance has a solution: options `sol` for the white squares (entries of `sol` at other squares are ignored) such that every numbered black square has exactly its number of b/w squares among its four neighbors, and every connected component of the white area is an open axis-parallel or `45°` rectangle. Feasibility does not include well-formedness; the decision problem requires both. A position beyond the end of a list reads as the default entry `[]`.
