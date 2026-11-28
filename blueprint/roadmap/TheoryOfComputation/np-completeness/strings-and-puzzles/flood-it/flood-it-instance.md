# Instances of FLOOD-IT

An instance of FLOOD-IT consists of a natural side length $n$, a list of natural colours of arbitrary length (read row by row: the tile in row $r$ and column $s$ has the colour at index $r n + s$) and a natural move bound $k$. The triple $(2, [\,], 0)$ is representable; the [board](board.md) reads a missing colour as zero, and the list length is checked by [validation](well-formed.md).
