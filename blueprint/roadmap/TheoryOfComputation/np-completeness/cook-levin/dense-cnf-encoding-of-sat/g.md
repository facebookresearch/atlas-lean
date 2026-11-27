# Work alphabet of the dense-SAT verifier

The work alphabet is $G = \{0,1\} \sqcup (\{0,1\} \cup \{\#\})$, the disjoint union of the bits and the bits
together with a separator. Its elements are the left symbols $\mathrm{inl}(b)$ for a bit $b$, the right symbols
$\mathrm{inr}(b)$ for a bit $b$, and the separator $\#$. This is the alphabet of the pair encoding.

Formula and assignment bits are stored on the work stacks as left symbols $\mathrm{inl}(b)$.
