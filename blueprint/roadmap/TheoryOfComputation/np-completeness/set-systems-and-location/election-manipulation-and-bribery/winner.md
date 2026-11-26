# Single-winner STV winner in SINGLE TRANSFERABLE VOTE MANIPULATION

In SINGLE TRANSFERABLE VOTE MANIPULATION, the single-winner STV winner for a candidate list $C$ and a list of ballots is optional. Starting from $C$, apply $|C| - 1$ [elimination rounds](eliminate.md) (with $|C|$ the length of the list $C$, and $|C| - 1 = 0$ when $C$ is empty); the winner is the first candidate of the remaining list. For a nonempty $C$ exactly one candidate remains and is the winner; for an empty candidate list there is no winner (the result is none).
