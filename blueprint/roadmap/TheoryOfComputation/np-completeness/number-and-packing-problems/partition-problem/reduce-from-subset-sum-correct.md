# Correctness of the encoded SUBSET-SUM to PARTITION reduction

For every bitstring $x$, SUBSET-SUM accepts $x$ if and only if [PARTITION](partition-dec.md)
accepts the image of $x$ under the
[encoded reduction from SUBSET-SUM to PARTITION](reduce-from-subset-sum.md); this includes the
bitstrings that encode no SUBSET-SUM instance.
