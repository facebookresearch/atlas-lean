# Number normalizer restores its work stacks and prepends its answer

Let $x$ and $o$ be bit strings and $v$ a Boolean. There is an internal state $v'$ such that the [payload normalizer
machine](a-linear-time-machine-for-total-binary-payload-n/prog.md), started at label $\mathrm{read}(\text{none})$
with internal state $v$, input $x$, empty buffer and output stack $o$, reaches label done with internal state $v'$,
empty input and buffer, and output stack equal to the
[normalization](normalizing-the-total-binary-natural-number-deco/normalize-nat.md) of $x$ followed by $o$, in at
most $2|x| + 3$ steps.
