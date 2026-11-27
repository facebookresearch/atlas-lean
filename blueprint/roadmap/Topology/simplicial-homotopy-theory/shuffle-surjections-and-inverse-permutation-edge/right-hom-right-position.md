# The right rank at an original right position is its block index

For p, q : ℕ and an ordered (p, q)-shuffle s, and i : Fin q, the right rank at the vertex
(s.perm (Fin.natAdd p i)).castSucc has value i.val. Thus exactly i.val right positions precede
that original right element's shuffled position.
