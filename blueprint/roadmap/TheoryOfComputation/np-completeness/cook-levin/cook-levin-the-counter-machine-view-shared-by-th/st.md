# Stacks holding given counter values

For a type $C$, counter values
$f : C \to \mathbb{N}$ and a list $o$ of Booleans, $\mathrm{st}(f, o)$ is the stack contents of a
counter machine whose output stack $\mathrm{out}$ holds $o$ and whose counter stack $c_x$ holds
exactly $f(x)$ copies of the unit symbol, for each $x \in C$.
