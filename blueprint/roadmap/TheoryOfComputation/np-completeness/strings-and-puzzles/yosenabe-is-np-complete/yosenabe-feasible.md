# Yosenabe solutions

A Yosenabe puzzle is feasible when there is a tip function assigning to each cell $x$ a cell $\mathrm{tip}(x)$ such that

- for every circle $x$, the tip $\mathrm{tip}(x)$ is a gray cell in the same row or the same column as $x$, and no cell on the line of the arrow from $x$ to $\mathrm{tip}(x)$ (the cells from $x$, excluded, to the tip, included) contains a circle;
- for distinct circles $x \ne x'$, the lines of their arrows share no cell;
- for every gray cell $g$ with nonzero label $a_g$, the numbers of the circles $x$ whose tip is in the same gray area as $g$ sum to $a_g$;
- for every gray cell $g$, some circle $x$ has its tip in the same gray area as $g$.
