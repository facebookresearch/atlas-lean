# Control labels of the SAT-to-3SAT emitter

The emitter machine has the labels
$\mathrm{start}$, $\mathrm{clause}$, $\mathrm{fin}$ and $\mathrm{done}$, and, for Booleans
$f, p, s, x, e$, the labels $\mathrm{lit}(f)$, $\mathrm{fa}(s, x)$, $\mathrm{fb}(s, x)$,
$\mathrm{fc}(s, x)$, $\mathrm{fd}(s, x)$, $\mathrm{fe}(s, x)$, $\mathrm{body}(f, p)$,
$\mathrm{cp}(f, e)$, $\mathrm{aft}(f)$ and $\mathrm{sfx}(f)$, all distinct; equality of labels is
decidable.

At $\mathrm{lit}(f)$ the machine pops a literal marker, $f$ telling whether it is the first
literal walked in its clause. The labels $\mathrm{fa}$ to $\mathrm{fe}$ prepend the fresh literal
$(2^{z+1} + 1, s)$ for the current counter $z$, where $x$ is the polarity of the pending literal
when $s$ is true and its first-literal flag when $s$ is false. The labels $\mathrm{body}$ and
$\mathrm{cp}$ prepend the renamed literal, and $\mathrm{aft}$ and $\mathrm{sfx}$ close the output
clause.
