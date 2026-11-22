# Edge-list decoder

The edge-list decoder reads a bit string as a list of pairs of natural
numbers, each number written in unary as that many $1$s followed by a $0$. On the empty string
it returns the empty list. Otherwise it reads a number $u$, then a number $v$, decodes the rest
recursively, and returns $(u, v)$ followed by the result; it fails if the input ends inside a
number or after an unpaired number, or if decoding the rest fails.

In a graph encoding it parses what follows the vertex count.
