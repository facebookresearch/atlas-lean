# Dense encoding of a clause

The bit string encoding a clause is the concatenation of the
two-bit codes of its slots, in order (empty slot $01$, positive literal $10$, negative literal
$11$), followed by the terminator $00$.
