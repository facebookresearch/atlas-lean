# Scan phases of the PARTITION doubling pass

The doubling pass reads a bitstring in one of three phases: start (at the first bit of a block),
marker (at a later marker bit of a block, or its final false) and payload (at a payload bit).
Here the input is read as blocks, each payload bit $c$ written as the two bits true, $c$ and each
block ended by a false bit.
