# List canonicalizer normalizes one element

Stack contents are listed from the top; $f(p)$ denotes the framed form $1 p_1 \cdots 1 p_m 0$ of a bit string $p$
and $\nu(p)$ its [normalization](../normalizing-the-total-binary-natural-number-deco/normalize-nat.md). Let $p$,
$x$, $a$, $o$ be bit strings and $v$ a Boolean. Started at label loop with internal state $v$, input $f(p)x$,
accumulator $a$, output $o$ and empty workspace stacks, the [list canonicalizer](prog.md) reaches label loop with
internal state $0$ (false), input $x$, accumulator $f(\nu(p))$ reversed followed by $a$, output $o$ and empty
workspace stacks in at most $8|f(p)|$ steps.
