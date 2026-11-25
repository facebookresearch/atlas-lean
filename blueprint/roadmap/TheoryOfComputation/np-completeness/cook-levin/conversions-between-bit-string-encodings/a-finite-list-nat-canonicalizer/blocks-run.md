# List canonicalizer normalizes a sequence of framed payloads

With the notation of [one element](element-run.md), let $p^1, \ldots, p^k$ be bit strings (not necessarily binary
codes), $X = f(p^1) \cdots f(p^k)$, $a$ and $o$ bit strings and $v$ a Boolean. Started at label loop with internal
state $v$, input $X$, accumulator $a$, output $o$ and empty workspace stacks, the [list canonicalizer](prog.md)
reaches label finish with internal state $0$ (false), empty input, accumulator
$f(\nu(p^1)) \cdots f(\nu(p^k))$ reversed followed by $a$, output $o$ and empty workspace stacks in at most
$8|X| + 1$ steps.
