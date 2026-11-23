# Loop-body stages of the cell-shift generator

For a symbol count $g$ and a window depth
$d$, the finite type of stages of the loop body of an $(i, k)$ block: for each flag $b$, two
stages adding the block base, four stages building the second base and two drain stages; one
stage for each stage of the multiplication routine; and for each clause kind $c$ (over $g$ and
$d$), a terminator stage, two stages loading the variable count, one stage for each literal
position $l < 3$ and each stage of the literal routine, and a finishing stage. The flag $b$ is
true in the in-range loop and false in the overflow loop.
