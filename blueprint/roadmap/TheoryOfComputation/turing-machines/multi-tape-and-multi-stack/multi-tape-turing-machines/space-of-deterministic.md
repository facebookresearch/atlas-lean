# Space of the deterministic computation path

Let $M$ be a deterministic multi-tape
Turing machine, $x$ an input and $t \in \mathbb{N}$. The number of work-tape cells visited along
the computation path of $M$ on $x$ made of the first $t$ steps from the initial configuration
equals the space used by the run of $M$ from the initial configuration on $x$ up to step $t$.
Both count the visited cells on each work tape separately and sum over the work tapes.
