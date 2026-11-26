# Number-pair projector normalizes both fields of a raw pair frame

Stack contents are listed from the top; $f(p)$ is the framed form $1 p_1 \cdots 1 p_m 0$ of a bit string $p$ and
$\nu(p)$ its [normalization](../normalizing-the-total-binary-natural-number-deco/normalize-nat.md). Let $p$, $r$,
$\ell$, $\rho$ be bit strings and $v$ a Boolean. There is an internal state $v'$ such that the [number-pair
projector](prog.md) goes from label $\mathrm{pair}(\mathrm{read})$, internal state $v$, splitter input $f(p) r$,
left output $\ell$, right output $\rho$ and all other stacks empty, to label good, internal state $v'$, left output
$\nu(p)\ell$, right output $\nu(r)\rho$ and all other stacks empty, in at most $2|f(p) r| + 6$ steps.
