# The decomposition returned by adjacent-inversion search

If the adjacent-inversion search returns `(p,i,j,s)`, then the input
list is `p ++ i :: j :: s` and the adjacent entries satisfy `j < i`.
The list entries lie in an arbitrary linearly ordered type.
