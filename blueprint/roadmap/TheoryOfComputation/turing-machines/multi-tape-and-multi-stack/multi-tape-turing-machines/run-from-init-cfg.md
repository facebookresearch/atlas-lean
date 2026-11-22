# Lockstep runs from the initial configuration

Let $M$ and $M'$ be deterministic machines
with $k$ work tapes over the same alphabet such that $M'$ simulates $M$ up to a state relabelling
$f$. Then for every input word $x$ and every $t \in \mathbb{N}$, the configuration of $M'$ after
$t$ steps on input $x$ is the configuration of $M$ after $t$ steps on input $x$ with its state
relabelled by $f$: a state $q$ becomes $f(q)$ and the halting state stays halting.
