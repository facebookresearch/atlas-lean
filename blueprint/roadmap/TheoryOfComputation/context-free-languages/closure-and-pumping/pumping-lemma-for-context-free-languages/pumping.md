# Pumping lemma for context-free languages

For every context-free language $L$ over an
alphabet $T$ there is a natural number $n > 0$ such that every word $w \in L$ with $|w| \ge n$
can be written as $w = uvxyz$ with words $u, v, x, y, z$ over $T$ such that $vy$ is nonempty,
$|vxy| \le n$, and $u v^i x y^i z \in L$ for every natural number $i$, where $v^i$ and $y^i$
denote the concatenations of $i$ copies of $v$ and of $y$.
