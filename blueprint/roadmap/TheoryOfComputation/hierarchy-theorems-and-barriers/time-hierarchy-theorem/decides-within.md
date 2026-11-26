# Deciding within a time bound

A code $c$ decides a decision problem $L$ within the time
bound $t : \mathbb{N} \to \mathbb{N}$ when, on every bit list $x$, the machine of $c$ started on the
input word of $x$ halts within $t(|x|)$ steps, and its tape from the head rightwards, without
trailing blanks, is the single symbol of the answer $L(x)$: $2$ for true and $1$ for false.
