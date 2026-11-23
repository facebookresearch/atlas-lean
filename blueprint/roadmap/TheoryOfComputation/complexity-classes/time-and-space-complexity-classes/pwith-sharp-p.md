# Polynomial time with a #P oracle

The class $\mathsf{P}^{\#\mathsf{P}}$ consists of the
decision problems $L$ for which there are a function $f$ in $\#\mathsf{P}$, polynomials $p$ and
$q$, and polynomial-time functions $\mathrm{next}$ and $\mathrm{final}$ such that, for every
bitstring $x$, $L(x)$ is true exactly when the following oracle machine outputs true on $x$.
Starting from the empty history $h$, it runs $p(|x|)$ rounds; in each round it computes the
query $y = \mathrm{next}(x, h)$ from $x$ and the history $h$ of queries and their natural-number
answers so far, and if $|y| \le q(|x|)$ it appends $(y, f(y))$ to $h$, while otherwise it skips
all remaining rounds. Finally it outputs $\mathrm{final}(x, h)$.
