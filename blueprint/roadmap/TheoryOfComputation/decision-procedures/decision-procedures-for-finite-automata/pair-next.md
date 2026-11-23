# Successors of a pair of states

Let $D$ and $E$ be encoded DFAs over the same alphabet,
and let $p \in \mathbb{N}$ code the pair of states $(s, t)$ under the pairing bijection
$\mathbb{N} \times \mathbb{N} \to \mathbb{N}$. The successors of $p$ form the list that has, for
each letter $a$ in the letters of $D$ followed by the letters of $E$, the code of the pair made of
the step of $D$ from $s$ on $a$ and the step of $E$ from $t$ on $a$.
