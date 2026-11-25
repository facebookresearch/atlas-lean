# Entry label of a literal

For Booleans $f$ and $p$, the label where the emitter continues
after popping the marker of a literal of polarity $p$ is $\mathrm{body}(\text{true}, p)$, which
copies the name directly, if $f$ holds (the literal is the first walked in its clause), and
$\mathrm{fa}(\text{true}, p)$, which first prepends the fresh literal of the current counter
with polarity true, otherwise.
