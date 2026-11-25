# Conv reduced left

Annihilation on the left: convolving the coaugmentation-side vanish
composite of a twisting cochain on the left gives zero. This is
`TwistingCochain.coaug_vanish` followed by `conv_zero_left`.
The unit comonoid is an explicit hypothesis because pinned Mathlib supplies
`ComonObj.instTensorUnit` only as a definition, deliberately not as a global
instance.
