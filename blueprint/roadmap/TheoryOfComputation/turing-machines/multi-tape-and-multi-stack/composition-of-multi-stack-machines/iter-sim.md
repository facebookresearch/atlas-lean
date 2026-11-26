# Simulation transports runs

Let $f$ be a partial function from a set $\alpha$ to itself and $g$ a partial function from a set
$\beta$ to itself (step functions, where being undefined means halting), and let $e : \alpha \to
\beta$ be a map such that, for all $c, c' \in \alpha$, whenever $f$ is defined at $c$ with value
$c'$, the function $g$ is defined at $e(c)$ with value $e(c')$. Say that $n$ steps of $f$ lead
from $c$ to $d$ if $f$ can be applied $n$ times in succession starting from $c$, each application
being defined, and the result is $d$ (zero steps lead from $c$ to $c$). Then for every
$n \in \mathbb{N}$ and all $c, d \in \alpha$, if $n$ steps of $f$ lead from $c$ to $d$, then $n$
steps of $g$ lead from $e(c)$ to $e(d)$.

Concretely, a run of $n$ steps is the $n$-th iterate of the extension of $f$ to $\alpha$ with an
added failure value $\bot$, which sends $\bot$ to $\bot$ and $c$ to $f(c)$ where $f$ is defined
and to $\bot$ elsewhere. Since $\bot$ is absorbing, an iterate that ends at an element $d$ of
$\alpha$ passes only through elements of $\alpha$, and every step along it is defined.
