# Flag bit of a machine state

A flag on a set $\sigma$ of machine states consists of a map $\mathrm{tag}$ from the bits
$\{\mathrm{false}, \mathrm{true}\}$ to $\sigma$ that stores a bit in a state and a map
$\mathrm{untag}$ from $\sigma$ to the bits that reads it back, such that
$\mathrm{untag}(\mathrm{tag}(\beta)) = \beta$ for every bit $\beta$. The program primitives use it
to branch on whether a pop found a symbol.
