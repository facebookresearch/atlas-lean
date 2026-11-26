# The init family of an encoding is a layout-level init family

Let $E$ be an encoding of a
machine $M$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, and let $m, T, H$ be
natural numbers. The init family of $E$ for $x, Y, m, T, H$ equals the layout-level init family
over the layout of $E$ with start code the code of the pair of the main label and the initial
state of $M$, stack $k_0$ the number of the input stack, code list the codes of the symbols of $Y$
in increasing order without repetitions, input codes the codes of the symbols of $x$, and the
same $m, T, H$.

The family of $E$ lists the certificate symbols $Y$ in their given order, possibly with repeated
codes; the equality holds because order and repetitions do not change these clauses.
