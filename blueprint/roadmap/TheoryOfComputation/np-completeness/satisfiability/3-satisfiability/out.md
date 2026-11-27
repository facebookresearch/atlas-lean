# Output of an emitter on a bit string

For an emitter $E$ with output map $g$ and a bit
string $x$: if the length-prefixed CNF decoder reads a CNF formula $\varphi$ from $x$ with no bits
left over, the output is $g(\varphi)$; otherwise it is the bit string that $E$ reserves as the
output for undecodable inputs.
