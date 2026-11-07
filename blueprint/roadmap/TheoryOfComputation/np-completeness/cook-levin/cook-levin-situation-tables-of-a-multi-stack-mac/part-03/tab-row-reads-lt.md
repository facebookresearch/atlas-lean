# Reads of the in-range shift stay in the row

Fix an encoding $E$ of a finite TM2 machine
and natural numbers $H$, $i$, $k$ and $j$. Write $p$ for the number of symbols situation $i$
leaves pushed on stack number $k$ and $n$ for the number of original symbols it consumes from
stack number $k$. If $p \le j$ and $j < (H \mathbin{\dot{-}} \max(p, n)) + p$, where $\dot{-}$ is
truncated subtraction, then $j - p + n < H$.

So every old cell that the table-driven row update reads lies in the row of height $H$.
