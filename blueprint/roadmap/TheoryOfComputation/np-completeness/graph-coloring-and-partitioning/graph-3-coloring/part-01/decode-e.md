# Decoding a graph

To decode a bit string $x$, read a unary number $n$ from the front of
$x$ ($n$ copies of true ended by false); if there is none, decoding fails. Otherwise decode the
rest of $x$ as an edge list $es$ (pairs of unary numbers until the input ends); if that fails,
decoding fails, and otherwise the result is the pair $(n, es)$.
