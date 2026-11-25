# Number-pair projector fails on malformed framing in linear time

Let $x$ be a bit string on which the [decoder of pairs of natural numbers](decode-pair-nat.md) fails, let $\ell$,
$\rho$ be bit strings and $v$ a Boolean. Started at label $\mathrm{pair}(\mathrm{read})$ with internal state $v$,
splitter input $x$, left output $\ell$, right output $\rho$ and all other stacks empty, the [number-pair
projector](prog.md) reaches label bad, with some internal state and some stack contents, in at most $|x| + 1$
steps. The work stacks may then hold partial contents.
