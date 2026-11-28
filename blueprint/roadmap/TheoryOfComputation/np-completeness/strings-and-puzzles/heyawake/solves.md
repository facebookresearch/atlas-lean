# Solutions of a HEYAWAKE grid

A painting $p$ of the cells of a HEYAWAKE grid with $m$ rows and $n$ columns ($p(r, c)$ true when cell $(r, c)$ is painted) solves the puzzle when:

1. no two painted cells share a side;
2. the unpainted cells form a nonempty set that is connected in the [grid graph](../choco-banana/grid.md);
3. every numbered room contains exactly as many painted cells as its number;
4. no horizontal or vertical run of consecutive unpainted cells meets three different rooms: if the cells $(r, c)$ with $c_1 \le c \le c_3$ are all unpainted and $c_1 < c_2 < c_3$, two of $(r, c_1), (r, c_2), (r, c_3)$ lie in the same [room](room-of.md), and likewise within a column.
