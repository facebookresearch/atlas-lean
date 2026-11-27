# To Nat List

Homogeneous natural-number list of the stored face indices, in stored order.
`nil` maps to `[]` and `snoc c i` maps to `c.toNatList ++ [i.val]`.
