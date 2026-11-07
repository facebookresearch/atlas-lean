# Universality of codes

**Universality of codes**, for machines that read bit inputs. Let $M$ be a single-tape
Turing machine with a finite alphabet $\Gamma$ and a finite set of states that contains the
initial state and is closed under the transitions of $M$, and let $\iota$ be an injective map
from the bits to $\Gamma$ whose values are not the blank. Then there are a code $c$ and an
injective map $f$ from $\Gamma$ to the natural numbers, sending the blank to $0$ and each
$\iota(b)$ to the symbol of the bit $b$, such that for every word $l$ over $\Gamma$, writing
$f(l)$ for the word obtained by applying $f$ to each letter: the decoded machine of $c$ halts on
$f(l)$ exactly when $M$ halts on $l$, and its result (the tape from the head rightwards when it
halts) is then the result of $M$ on $l$ with $f$ applied to each cell; and for every
$T \in \mathbb{N}$, the decoded machine of $c$ halts within $T$ steps on $f(l)$ if and only if
$M$ halts within $T$ steps on $l$.

(So the alphabet has at least three symbols; a machine over a smaller alphabet cannot read a bit
input.)
