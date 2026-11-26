# An inverted adjacent swap removes one inversion

Swapping adjacent entries `i,j` with `j < i` reduces the inversion count
by exactly one, regardless of the surrounding prefix and suffix:
`inversionCount (p ++ j :: i :: s) + 1 = inversionCount (p ++ i :: j :: s)`.
