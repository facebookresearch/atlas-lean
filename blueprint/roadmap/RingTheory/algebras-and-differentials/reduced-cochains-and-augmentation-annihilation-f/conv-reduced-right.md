# Conv reduced right

Annihilation on the right: convolving the augmentation-side vanish
composite of a twisting cochain on the right gives zero. This is
`TwistingCochain.aug_vanish` followed by `conv_zero_right`
(the pinned `MonObj` unit instance needs no extra hypothesis).
