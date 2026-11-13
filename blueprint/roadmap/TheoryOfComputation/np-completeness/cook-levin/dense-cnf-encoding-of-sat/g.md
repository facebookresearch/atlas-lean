# Work alphabet of the dense-SAT verifier

The work alphabet $G$ is the disjoint union of
the Booleans and the optional Booleans. Its elements are the left symbols $\mathrm{inl}(b)$ and
the right symbols $\mathrm{inr}(o)$, where $b$ is a Boolean and $o$ is either
$\mathrm{some}\ b$ or $\mathrm{none}$. This is the alphabet of the pair encoding, in which
$\mathrm{inr}(\mathrm{none})$ is the separator $\#$.

Formula and assignment bits are stored on the work stacks as left symbols $\mathrm{inl}(b)$.
