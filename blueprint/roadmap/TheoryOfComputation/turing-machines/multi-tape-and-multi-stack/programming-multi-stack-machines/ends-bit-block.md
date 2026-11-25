# End of a bit block

Let $d$ be a decoder that reads each symbol either as a bit or as a
marker. A list of symbols $A$ (the rest of a stack below a block) ends a bit block under $d$ when
$A$ is empty or $d$ reads its first symbol as a marker.
