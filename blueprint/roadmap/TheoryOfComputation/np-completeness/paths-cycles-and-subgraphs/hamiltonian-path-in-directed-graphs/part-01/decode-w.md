# Witness decoder

The witness decoder reads a list $w$ of bits as a list of natural numbers.
On the empty list it returns the empty list. Otherwise it reads a unary number $v$ from the front
of $w$, a run of $v$ copies of true ended by false, and if decoding the remaining bits gives a
list $p$, it returns $v$ followed by $p$. It fails if no unary number can be read from a
nonempty list, or if decoding the remaining bits fails.
