# Labels of the dense-to-binary converter

The labels of the dense-to-binary converter
program are the moving label $\mathrm{mv}$; the reading label $\mathrm{rd}(\iota)$ for a Boolean
$\iota$; the second-read label $\mathrm{rd2}(\iota, s)$ for Booleans $\iota$ and $s$; the two
literal labels $\mathrm{litA}$ and $\mathrm{litB}$; the two closing labels $\mathrm{eN}$ and
$\mathrm{eK}$; the clearing label $\mathrm{fK}(\iota)$ for a Boolean $\iota$; the literal-count
label $\mathrm{fN}$; and the clause-count label $\mathrm{fM}$. Equality of labels is decidable.

Here $\iota$ records whether a clause is open, and $s$ is the first bit read of a slot.
