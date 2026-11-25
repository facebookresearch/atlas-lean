# Solves

The rotation $\mathrm{rot}(r, c)$ of each tile closes the pipe system: for every cell $(r, c)$
of the $m \times n$ grid and every side of its rotated tile that has a pipe end, the
neighbouring cell across that side lies in the grid, and the rotated tile there has a pipe end
on the side facing back. In particular no pipe end may point off the board.
