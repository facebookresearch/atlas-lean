# One round of the membership procedure

Write $\langle s, t \rangle$ for the pairing
bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ given by $\langle s, t \rangle = t^2 + s$
if $s < t$ and $\langle s, t \rangle = s^2 + s + t$ otherwise. Given an encoded grammar $g$, a
word $w$ and a list $R$ of items found so far, the round lists, for every production
$A \to \rho$ of $g$, every position $j \le |w|$ and every start $i$ of $\rho$ for the factor of
$w$ ending at $j$ given $R$, the code $\langle A, \langle i, j \rangle \rangle$ of the item
$(A, i, j)$.
