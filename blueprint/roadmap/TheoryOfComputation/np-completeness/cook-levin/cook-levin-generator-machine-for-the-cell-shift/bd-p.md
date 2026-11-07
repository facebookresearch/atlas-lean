# Loop body of the cell-shift generator

For a layout $L$ with $g$ symbol codes and a block
$(i, k)$, the generator's statement at each loop-body stage, with flag $b$ true in the in-range
loop and false in the overflow loop: add the counter $KB$ to the counter $CB$; when $b$ is true,
add the product of the counters $U$ and $Gc$ to $CB$; add $CB$ and then the counter $Wc$ to the
counter $CW$; then start the in-range clauses for the symbols $x = g - 1, \dots, 0$ when $b$ is
true, and the overflow clause otherwise. A clause $c$ (in-range, overflow or pushed fill)
prepends the terminator $00$ to the output, adds the counter $Vc$ to the counter $P$, runs the
literal routines of $c$ from the last down to the first, drains $P$ prepending $01$ per unit, and
goes on to the next clause of its chain; after the last pushed-fill clause it returns to the
fill drain of the block setup, and after the last in-range clause and after the overflow clause
the drain stages empty $CB$ and then $CW$ and return to the head of the in-range loop when $b$ is
true, and of the overflow loop otherwise.
