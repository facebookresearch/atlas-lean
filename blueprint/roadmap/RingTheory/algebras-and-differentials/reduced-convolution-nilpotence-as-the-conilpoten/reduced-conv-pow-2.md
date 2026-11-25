# Reduced Conv Pow

Every sigma-valued reduced-convolution iterate of a reduced cochain is
reduced at its actual hidden degree, by induction consuming the induction
hypothesis through `IsReducedCochain.conv_of_left` with arbitrary right
factor `f`. Preservation only; not nilpotence and not support.
