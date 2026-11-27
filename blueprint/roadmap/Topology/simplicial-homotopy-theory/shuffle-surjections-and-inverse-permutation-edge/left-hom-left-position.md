# The left rank at an original left position is its block index

For p, q : ℕ and an ordered (p, q)-shuffle s, and i : Fin p, the left rank at the vertex
(s.perm (Fin.castAdd q i)).castSucc has value i.val. Equivalently, exactly i.val left
positions precede the shuffled position of the i-th original left element.
