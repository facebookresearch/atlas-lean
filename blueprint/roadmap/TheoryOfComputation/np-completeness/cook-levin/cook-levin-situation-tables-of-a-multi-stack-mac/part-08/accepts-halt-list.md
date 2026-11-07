# Acceptance of a halting configuration

Let $M$ be a machine, $l'$ a list over its output
alphabet and $\mathrm{acc}$ an output symbol. The halting configuration with output $l'$ (halted,
in the initial state, with $l'$ on the output stack and every other stack empty) is accepting for
$\mathrm{acc}$ if and only if $l'$ is nonempty and its first element is $\mathrm{acc}$.
