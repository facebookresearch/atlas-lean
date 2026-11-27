# Every partial recursive description method has a code

Let $D$ be a partial recursive
function from binary strings to binary strings. Then there is a code $c$ for a partial recursive
function such that running $c$ equals $D$ as a partial function: for every binary string $w$,
running $c$ on $w$ is defined exactly when $D(w)$ is, and then has the same value.
