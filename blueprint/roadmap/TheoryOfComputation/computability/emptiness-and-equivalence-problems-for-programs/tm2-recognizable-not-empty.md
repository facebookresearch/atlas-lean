# Nonemptiness is recognizable

The set of codes of partial recursive functions
$\mathbb{N} \to \mathbb{N}$ that are defined on at least one input is recognizable by
multi-stack machines: some multi-stack machine halts on the binary encoding of a code $c$ exactly
when the function coded by $c$ is defined on some input.

The machine searches for an input $n$ and a step bound $k$ such that the evaluation of $c$ on $n$
halts within $k$ steps.
