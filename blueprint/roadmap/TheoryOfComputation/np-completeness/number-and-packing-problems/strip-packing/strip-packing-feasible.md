# Feasible strip packings

A strip packing instance $(R, W, H)$ with
$R = ((w_1, h_1), \dots, (w_n, h_n))$ is feasible when there are natural numbers
$x_1, y_1, \dots, x_n, y_n$ such that $x_j + w_j \le W$ and $y_j + h_j \le H$ for every
$1 \le j \le n$, and for all $1 \le a < b \le n$ at least one of $x_a + w_a \le x_b$,
$x_b + w_b \le x_a$, $y_a + h_a \le y_b$ and $y_b + h_b \le y_a$ holds.

That is, the unrotated rectangles with lower-left corners $(x_j, y_j)$, widths $w_j$ and heights
$h_j$ lie in $[0, W] \times [0, H]$, and any two of them are separated by a vertical or a
horizontal line. When all widths and heights are positive, the latter says that no two of the
rectangles overlap in their interiors.
