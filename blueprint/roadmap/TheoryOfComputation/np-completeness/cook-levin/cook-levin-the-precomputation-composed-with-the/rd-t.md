# The read loop

Given a code map $c_f$ from the raw alphabet $\mathrm{Fin}\,r$ to the code
alphabet $\mathrm{Fin}\,g$, a separator code $c_s$ and a list $L$ of raw symbols, the read-loop
statement tests the symbols $i$ of $L$ in order against the top of the raw input stack. At the
first $i$ found on top, it pops it, pushes $c_f(i)$ on the host input stack and one unit on the
scratch counter $N$, and goes back to the read-loop label (with the flag true). If no symbol of
$L$ is on top, in particular when the raw input is empty, it pushes $c_s$ on the input stack, sets
the flag to false and goes to the first label of the counter program.

The full program takes $L$ to be all of $\mathrm{Fin}\,r$, so each step reads one input symbol.
