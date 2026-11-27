# Depth-two weighted threshold circuits

A *depth-two weighted threshold circuit* ($\mathrm{THR}\circ\mathrm{THR}$) on $n$ inputs consists of bottom gates $g_1,\dots,g_t$, each a weighted threshold function $g_j(x)=[\sum_i a_{ji}x_i\ge\theta_j]$ with real weights, and a top weighted threshold gate applied to $g_1(x),\dots,g_t(x)$ (in a variant, the top gate may also read the inputs directly). Its *gate count* is $t+1$ and its *wire count* is the number of nonzero weights.

## Depends on

- [Threshold gates and the basis of threshold circuits](../../parallel-circuit-hierarchies/threshold-gates-and-threshold-circuits.md)

## Sources

- Daniel M. Kane, Ryan Williams, "Super-Linear Gate and Super-Quadratic Wire Lower Bounds for Depth-Two and Depth-Three Threshold Circuits", Proceedings of the Forty-Eighth Annual ACM Symposium on Theory of Computing (STOC 2016), 2016 (LTF ∘ LTF circuits, gate and wire counts).
- András Hajnal, Wolfgang Maass, Pavel Pudlák et al., "Threshold Circuits of Bounded Depth", Journal of Computer and System Sciences 46(2), 1993.
