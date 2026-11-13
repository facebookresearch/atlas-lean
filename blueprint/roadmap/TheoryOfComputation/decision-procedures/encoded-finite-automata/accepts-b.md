# Membership test for encoded NFAs

For an encoded NFA $N$ and a word $w$, the membership
test is the Boolean that is true exactly when some state reached on $w$ is an accepting state of
$N$. The states reached on $w$ are computed from the ε-closure of the start states by, for each
letter of $w$ in turn, following the transitions on that letter and taking the ε-closure.
