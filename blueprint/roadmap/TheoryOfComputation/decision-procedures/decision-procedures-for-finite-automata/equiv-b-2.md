# Equivalence test for encoded DFAs

Let $D$ and $E$ be encoded DFAs over an alphabet
$\alpha$ with decidable equality. The equivalence test of $D$ and $E$ is the Boolean that is true
exactly when, for every entry $p$ of the list of reachable pairs of states of $D$ and $E$, writing
$p = \langle s, t \rangle$ with the pairing function $\langle s, t \rangle$, equal to $t^2 + s$ if $s < t$ and to $s^2 + s + t$ otherwise, $s$ is in the accepting list of $D$ if
and only if $t$ is in the accepting list of $E$.

It returns true exactly when $D$ and $E$ have the same language.
