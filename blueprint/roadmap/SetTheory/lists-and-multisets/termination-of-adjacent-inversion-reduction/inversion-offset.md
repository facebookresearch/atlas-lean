# The length offset for inversion weights

The length-dependent offset with `inversionOffset 0 = 0` and
`inversionOffset (n + 1) = inversionOffset n + n*n + 1`. Its successive
increments exceed the inversion-count bound for lists of length `n`.
