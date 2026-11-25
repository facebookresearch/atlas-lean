# Feasible KURODOKO (KUROMASU) instances

A KURODOKO instance $(w, h, \mathrm{clues})$ is feasible when some set $B$ of black squares of
the $h \times w$ grid satisfies the rules: (1) no clue square is black; (2) no two black squares
are horizontally or vertically adjacent; (3) the white squares form a connected region of the
grid; (4) for each clue square $v$ with value $N$, exactly $N$ squares are visible from $v$,
where a square is visible from $v$ when it lies in the same row or column and every square of
the segment between them, both ends included, is white. The clue square itself counts as
visible.
