# Positional strategy in a parity game

Let $G$ be a parity game: positions owned by two players, a move relation in which every position
has at least one move, and a priority in $\mathbb{N}$ for each position.
A positional (memoryless) strategy for a player $p$ is a map that chooses a successor position at
every position, such that at every position owned by $p$ the chosen successor is a legal move. Its
values at the positions of the other player play no role.
