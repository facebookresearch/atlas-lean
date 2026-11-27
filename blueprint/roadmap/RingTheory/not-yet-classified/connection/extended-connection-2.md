# Extended Connection

A connection extends to the tensor products with all exterior powers of `Omega`. On a pure
tensor its value is the wedge of the connection term with the form, plus the coefficient tensored
with the descended de Rham differential of the form.

`S` is not de Rham data: `Stacks.DeRham.DifferentialDescent.sourceDeRham` constructs the de Rham
complex of `B` over `A` ([Stacks, Tag 0FKF]) and
`Stacks.DeRham.DifferentialDescent.SourceDeRham.eq_sourceDeRham` proves it is the only term of
`SourceDeRham A B`, so `S` names that complex; its square-zero property is derived from the
defining rule on generators by `Stacks.DeRham.DifferentialDescent.comp_eq_zero_of_gen`.  The
quotient `π : Ω[B⁄A] → Omega` with `hπ` and `hgen` is the setting [Stacks, Tag 07I0] itself
fixes, by reference to [Stacks, Tag 07HY].
