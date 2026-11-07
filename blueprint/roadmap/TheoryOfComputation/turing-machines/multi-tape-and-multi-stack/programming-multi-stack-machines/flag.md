# Flag bit of a machine state

A flag on a type $\sigma$ of machine states consists of a map
$\mathrm{tag} : \mathrm{Bool} \to \sigma$ that stores a bit in a state and a map
$\mathrm{untag} : \sigma \to \mathrm{Bool}$ that reads it back, such that
$\mathrm{untag}(\mathrm{tag}(\beta)) = \beta$ for every bit $\beta$. The program primitives use it
to branch on whether a pop found a symbol.
