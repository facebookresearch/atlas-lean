# Decoding a complete length-prefixed CNF formula

Given a bit string $w$, the decoder reads
one CNF formula $\varphi$ from the front of $w$ with the length-prefixed CNF decoder, which also
returns the bits left after $\varphi$. The result is $\varphi$ if no bits are left; decoding fails
if no formula can be read or if bits remain after it.
