# Simulation transports runs

Let $f : \alpha \to \mathrm{Option}\,\alpha$ and
$g : \beta \to \mathrm{Option}\,\beta$ be partial step functions (a value $\mathrm{none}$ means
halting) and $e : \alpha \to \beta$ a map such that $f(c) = c'$ implies $g(e(c)) = e(c')$ for all
$c, c'$. Then for every $n$ and all $c, d \in \alpha$, if $n$ steps of $f$ starting from $c$ end
at $d$, then $n$ steps of $g$ starting from $e(c)$ end at $e(d)$.

Halted configurations are absorbing, so every intermediate configuration of such a run is live.
