# MATRIX COVER with a positive definite matrix is NP-complete

The decision problem MATRIX COVER with a positive definite matrix is NP-complete: it belongs to
NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

The entries are nonnegative integers and the question asks for a sign vector with value at most
$K$. Garey and Johnson (1979), [MS13], comment, records the positive definite case for the printed
question with $\ge K$; for that direction the all-ones vector maximizes the sum, so the credited
$\le K$ question needs the following reduction from MAX CUT. For the adjacency matrix $A$ of a
nonempty simple graph on $n$ vertices, $A + nI$ is positive definite by strict diagonal dominance,
and its value on a sign vector is $n^2 + 2|E| - 4c$, where $c$ is the number of cut edges; so a cut
of size at least $k$ exists exactly when some sign vector has value at most $n^2 + 2|E| - 4k$.

Source: Garey and Johnson (1979), [MS13], comment (for the printed $\ge K$ question).
