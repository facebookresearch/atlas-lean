# One halving step of the binary conversion (SUBSET-SUM reduction machine)

Let $c$ and $p$
be natural numbers, $r$ a bit (read as $0$ or $1$ in arithmetic), $v$ a value of the machine's
Boolean flag and $S$ an assignment of contents to the stacks. Suppose stack $A$ holds $2c + r$
copies of the unit symbol and stack $H$ holds $p$ copies. Then, starting at label $\mathrm{hv0}$
with flag $v$ and stacks $S$, the machine reaches label $\mathrm{hvB}$ in exactly $2c + r + 1$
steps, with some flag $v'$ and stacks $S'$ such that $S'(A)$ is empty, $S'(H)$ holds $p + c$
copies of the unit symbol, $S'(T)$ is the input-bit symbol $\mathrm{bit}(r)$ on top of $S(T)$,
and every stack other than $A$, $H$, $T$ holds the same contents as in $S$.
