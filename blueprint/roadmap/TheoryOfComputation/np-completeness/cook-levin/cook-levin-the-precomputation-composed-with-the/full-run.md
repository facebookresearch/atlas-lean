# The composed machine, raw input to formula

Let $M$ be a finite multi-stack Turing machine with encoding data $E$, let $Y$ be a list of input-stack symbols of
$M$, $a$ an output-stack symbol, $\iota$ a map from the raw symbols $\{0, \dots, r - 1\}$ to input-stack symbols,
$\sigma$ an input-stack symbol (the separator), $k$ a polynomial with natural-number coefficients and
$c, e \in \mathbb{N}$. Let $s = s_1 \cdots s_n$ be a raw input and $o$ a list of Booleans, and write
$x = \iota(s_1) \cdots \iota(s_n)\, \sigma$, $m = n + 1 + k(n)$ and $T = (m + c)^e$.

Then there are a flag $v$ and stack contents $S$ such that the [full program on the real generators](full-prog.md)
for $E$, $Y$, $a$, $\iota$, $\sigma$, $k$, $c$, $e$ goes from the read-loop label with flag false, $s$ on the raw
input stack, $o$ on the host output stack and every other stack empty, to the host's final label with flag $v$ and
stacks $S$ in at most the [step bound of the full machine](full-b.md) for $E$, $Y$, $k$, $c$, $e$ at $n$, and the
host output stack of $S$ holds the dense encoding of the [formula emitted by the
host](../cook-levin-the-five-generators-as-sub-machines-o/phi.md) $\Phi(x, Y, a, m, T)$ followed by $o$.

There is no further hypothesis: $|x| = n + 1 \le m$ holds automatically.
