# Cost bound for the witness clause check

Let $N$ be a list of natural numbers, $w$ a list
of booleans and $C$ a CNF clause, viewed as a list of $\ell$ literals (repetitions counted). The
cost of checking $C$ against $N$ and $w$ is at most $\ell \cdot (|N| + 1)$, where $|N|$ is the
length of $N$.

Each literal examined costs one tick plus one lookup, and a lookup costs at most $|N|$.
