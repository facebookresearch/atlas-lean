# Decoding a fixed number of literals

For a natural number $n$ and a bit string $w$, the
decoder reads $n$ literals one after another from the front of $w$ with the literal decoder. The
result is the clause made of these literals, in order, together with the bits left after them;
for $n = 0$ it is the empty clause together with $w$. Decoding fails if one of the $n$ literals
cannot be read.
