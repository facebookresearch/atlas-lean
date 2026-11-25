# Single-winner STV winner in SINGLE TRANSFERABLE VOTE MANIPULATION

In SINGLE TRANSFERABLE VOTE MANIPULATION, the single-winner STV winner: the last remaining candidate after `|C| - 1` eliminations, given by `((eliminate ballots)^[C.length - 1] C).head?`. Subtraction is natural-number subtraction, so `a - b = 0` whenever `a ≤ b`.
