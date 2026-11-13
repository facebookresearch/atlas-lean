# Number of blocks after one round

Let $M$ be a DFA with transition function $\delta$, let
$P$ be a list of sets of states, $C$ a set of states and $a$ a letter, and let
$\mathrm{pre} = \{q : \delta(q, a) \in C\}$. The partition after the splitter $(C, a)$, which
replaces each entry $D$ of $P$ meeting both $\mathrm{pre}$ and its complement by
$D \cap \mathrm{pre}$ and $D \setminus \mathrm{pre}$, has length equal to the length of $P$ plus
the number of entries of $P$ (counted with repetition) that meet both $\mathrm{pre}$ and its
complement.
