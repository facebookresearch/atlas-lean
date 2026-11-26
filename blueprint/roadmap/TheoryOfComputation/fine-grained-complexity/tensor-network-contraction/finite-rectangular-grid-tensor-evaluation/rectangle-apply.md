# Applying a rectangle kernel to its diagonal ends

Let $G$ be an integer-valued kernel of four labels, $\ell$ a matrix of labels indexed by pairs of
grid cells, and $\omega = ((r_1, r_2), (c_1, c_2))$ a rectangle. Applying $G$ to $\omega$ gives

$$G\bigl(\ell((r_1,c_1),(r_2,c_2)), \ \ell((r_1,c_2),(r_2,c_1)), \ \ell((r_2,c_1),(r_1,c_2)), \ \ell((r_2,c_2),(r_1,c_1))\bigr),$$

the four directed half-edges along the two diagonals of the rectangle.
