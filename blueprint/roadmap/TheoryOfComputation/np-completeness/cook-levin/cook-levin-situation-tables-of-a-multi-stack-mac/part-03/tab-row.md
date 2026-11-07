# The table-driven row update

Fix an encoding $E$ of a finite TM2 machine, a row height $H$,
a situation $i$ and an old row $\mathrm{old}$ giving a code for each stack number $k$ and depth
$j$. For a stack number $k$, write $p$ for the number of symbols situation $i$ leaves pushed on
stack $k$ and $n$ for the number of original symbols it consumes from stack $k$. The updated row
at $(k, j)$ is the code of the symbol situation $i$ leaves at depth $j$ of stack $k$ if $j < p$;
otherwise it is $\mathrm{old}(k, j - p + n)$ if $j < (H \mathbin{\dot{-}} \max(p, n)) + p$, where
$\dot{-}$ is truncated subtraction; otherwise it is $0$, the empty cell.

These are the three cases the shift clauses force: pushed fill, in-range shift and overflow.
