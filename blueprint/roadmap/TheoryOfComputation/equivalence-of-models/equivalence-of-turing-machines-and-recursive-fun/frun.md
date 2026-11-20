# Iterated steps of the wrapped machine

Let $c$ be a partial recursive code and let $s$ be
the map that sends none to none and a configuration $d$ of the wrapped machine for $c$ to the
result of one step of the wrapped machine on $d$ (which is none if $d$ has halted). For
$j \in \mathbb{N}$ and $x$ either a configuration of the wrapped machine for $c$ or none, the
$j$-fold run from $x$ is $s^{j}(x)$, the result of applying $s$ to $x$ $j$ times.
