# Feasibility of a ZEIGER grid

A ZEIGER instance $I$ is feasible when there is a function $v$ assigning a natural number to every grid position $x$ such that:

- $v(x) > 0$ for every $x$;
- if $\mathrm{cell}_I(x) = (d, a)$ with $a \neq 0$, then $v(x) = a$;
- for every $x$, $v(x)$ equals the number of distinct values of $v$ on the cells along the arrow of $x$:

    $$v(x) = \bigl\lvert \{\, v(y) : y \text{ lies along the arrow of } x \,\} \bigr\rvert.$$
