# Correctness of the encoded PARTITION to SUBSET-SUM reduction

For every bitstring $x$, [PARTITION](partition-dec.md) accepts $x$ if and only if SUBSET-SUM
accepts the image of $x$ under the
[encoded reduction from PARTITION to SUBSET-SUM](reduce-to-subset-sum.md); this includes the
bitstrings that do not decode as a list of natural numbers, and those that decode only with a
noncanonical payload.
