# Definedness of the clocked evaluator

For a code $c$, a list of bits $x$ and a clock
$T \in \mathbb{N}$, the clocked evaluator of $c$ on $x$ with clock $T$ returns a value if and
only if the simulation of $c$ has no step from the configuration after $T$ clocked steps on $x$
(the configuration after $T$ steps, or the halting configuration if the machine halts
earlier).
