# Strong limit cardinals are closed under exponentiation

A strong limit `κ` is closed under cardinal exponentiation: `x ^ y ≤ 2 ^ (x * y)`
(via `cantor` and `power_mul`), and `x * y < κ` by `mul_lt_of_lt`.  No
infiniteness hypothesis is needed — it is automatic by `IsStrongLimit.aleph0_le`.

## Sources

- Below a strong limit κ, x < κ and y < κ imply x ^ y < κ.
