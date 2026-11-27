# Instances of SURAROMU

An instance is a triple of a board given row by row ($\mathrm{true}$ for a black cell, $\mathrm{false}$ for a white one), the circle cell $(r, c)$ with its number, and the gates, each $(r, c, \ell, v, k)$: the $\ell$ cells starting at $(r, c)$ and going down (to higher rows) when $v$ is true and right (to higher columns) otherwise, with order number $k$, where $k = 0$ means the gate is unnumbered.
