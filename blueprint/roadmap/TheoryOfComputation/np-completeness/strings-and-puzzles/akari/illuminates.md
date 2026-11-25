# Illumination on an Akari board

Let $B$ be a board, a list of rows of natural numbers, and
write $B_{r,c}$ for the entry in row $r$ and column $c$, read as $1$ when there is no such entry. A
bulb at $(b_r, b_c)$ illuminates the cell $(r, c)$ when either $b_r = r$ and $B_{r,c'} = 0$ for
every column $c'$ strictly between $b_c$ and $c$, or $b_c = c$ and $B_{r',c} = 0$ for every row
$r'$ strictly between $b_r$ and $r$. In particular, a bulb illuminates its own cell.
