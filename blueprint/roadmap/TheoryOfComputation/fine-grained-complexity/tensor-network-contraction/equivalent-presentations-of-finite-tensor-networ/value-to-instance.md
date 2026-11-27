# Converting a factored network to an instance preserves value

Let $N$ be a factored tensor network on a finite linearly ordered vertex set $J$, $\Lambda$ a
finite set of labels in a type $A$, $d \in A$, and for each pair $a, b$ let $D_{a,b}$ be a finite
subset of $A$ and $\delta_{a,b}$ a map from $A$ to the labels of $N$. Assume that for all $a < b$,
$D_{a,b} \subseteq \Lambda$ and $\delta_{a,b}$ restricts to a bijection from $D_{a,b}$ onto
$\Theta_{a,b}$. Then the value of the complete-graph instance of $N$ (built from $D$ and $\delta$),
with labels $\Lambda$ and default $d$, equals the value of $N$.
