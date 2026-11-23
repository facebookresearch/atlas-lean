# Stack index of a literal in a transition clause

For a layout with $K$ stacks and window
depth $d$, the stack index $k_A(j)$ of literal $j$ is $\lfloor (j - 1)/d \rfloor$ when
$1 \le j \le Kd$, and $0$ when $j = 0$ or $j > Kd$.

With the row offset $k_B$ and the constant offset $c_i$ of situation $i$, the position of literal
$j$ of clause $(t, i)$ at height $H$ is $tW + k_A(j)\,Hg + k_B(j)\,W + c_i(j)$, where $g$ is the
number of symbol codes and $W$ the number of variables per time step.
