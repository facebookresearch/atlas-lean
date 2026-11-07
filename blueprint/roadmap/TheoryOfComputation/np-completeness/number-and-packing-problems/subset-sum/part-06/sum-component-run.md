# SUBSET-SUM verifier computes the mask-selected sum

On canonical delimited `encodeNat` blocks, the existing component
leaves the selected sum at a halt label. Normalize raw payloads first:
malformed blocks can instead reject early, leaving only a partial sum.
The cost uses framed bit length, never numeric magnitudes. The mask is
consumed; copy it before reuse in another component.
