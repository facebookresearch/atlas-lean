# The code of a finite-state binary machine

Let $M$ be a machine over the binary alphabet
with $k$ work tapes and a finite set of states $Q$, and let $e : Q \to \mathbb{N}$. The code of
$M$ with states numbered by $e$ has one table entry for each state $q \in Q$, symbol $a$ under
the input head and symbols $w$ under the $k$ work heads (each a bit or blank): its key is
$(e(q), a, w)$ and its value is the coded action of $M$ in state $q$ reading $a$ and $w$, with
the successor state numbered by $e$. The entries are listed in an unspecified order.

When $e$ is injective and sends the initial state of $M$ to $0$, the machine of this code
simulates $M$ up to the relabelling $e$.
