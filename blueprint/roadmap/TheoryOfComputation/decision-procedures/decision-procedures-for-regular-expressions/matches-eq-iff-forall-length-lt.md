# Short distinguishing words

Two regular expressions $r$ and $s$ denote the same language if
and only if every word of length less than $2^{n(r) + n(s)}$, where $n$ denotes the Thompson state
count, is matched by $r$ exactly when it is matched by $s$.

The bound is the number of states of the product of the subset-construction DFAs of the Thompson
automata.
