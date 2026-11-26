# One iteration of the time loop of the shift generator

Let $L$ be a layout with $g$ symbol
codes, let $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ be situation tables, let
$N, T, H, t \in \mathbb{N}$ with $t < T$, and suppose the tables are well formed for $N$
situations at height $H$. Write $W$ for the number of variables per time step at height $H$ and
$V = (T + 1) W$ for the number of variables. Let $F$ be counter values of the cell-shift generator
with empty scratch counters, with $\mathrm{Vc} = V$, $\mathrm{Gc} = g$, $\mathrm{Wc} = W$,
$\mathrm{Tn} = t$, $\mathrm{HG} = H g$ and $\mathrm{Hs} = H$, and with $\mathrm{P}$,
$\mathrm{TW}$, $\mathrm{TW1}$, $\mathrm{KB}$, $\mathrm{U}$, $\mathrm{Ui}$, $\mathrm{R}$,
$\mathrm{Ri}$, $\mathrm{Ka}$, $\mathrm{CB}$ and $\mathrm{CW}$ all $0$. Then for every output list
$o$ and every Boolean state $v$ there is a Boolean state $v'$ such that the generator, started at
the label $\mathrm{tw}(\mathrm{head})$ (the first stage of the time-loop multiplication) in state
$v$ with counters $F$ and output $o$, reaches the time-loop head $\mathrm{tHead}$ within at most
the step budget for one time step of the shift generator for $L$, $N$, $T$, $H$, in state $v'$
with counters $F$ and output the encoded blocks of time step $t$ followed by $o$.
