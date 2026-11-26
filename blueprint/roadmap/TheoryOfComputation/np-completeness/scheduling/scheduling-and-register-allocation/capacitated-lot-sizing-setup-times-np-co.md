# CAPACITATED LOT SIZING WITH SETUP TIMES is NP-complete

The [decision problem](capacitated-lot-sizing-setup-times-dec.md) CAPACITATED LOT SIZING WITH SETUP TIMES belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Hardness comes from a special case: BIN PACKING with $N$ pieces and $0 < K < N$ bins reduces to the instances with one period per bin, of capacity the bin size, and one item per piece, with setup time the piece size, processing time $0$ and demand $1$ in the last period (the output has $O(N^2)$ numbers). A BIN PACKING instance with $K = 0$ is a yes-instance exactly when $N = 0$, and one with $K \ge N$ exactly when every piece fits in a bin; these are decided directly and mapped to a fixed yes- or no-instance, so the output stays polynomial when $K$ is large; this restriction to setup and processing times that depend only on the item keeps the problem NP-hard.

## Sources

- W. W. Trigeiro, L. J. Thomas and J. O. McClain, "Capacitated lot sizing with setup times", Management Science 35 (1989), 353-366, doi:10.1287/mnsc.35.3.353, p. 359.
- I. Fragkos, Z. Degraeve and B. De Reyck, "A horizon decomposition approach for the capacitated lot-sizing problem with setup times", INFORMS Journal on Computing 28 (2016), 465-482, doi:10.1287/ijoc.2016.0691, Sections 3 and 6.5.1.
