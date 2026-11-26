# Threshold Counter Gates

Threshold-`T` counter gates under layout `L`: inputs at
`L (Fin.castAdd _ (Fin.castSucc i))`, target at
`L (Fin.castAdd _ (Fin.last k))`, work cells at
`L (Fin.natAdd (k + 1) j)`. Unary one-hot construction (compute,
threshold, uncompute); the theorems below are its contract.
