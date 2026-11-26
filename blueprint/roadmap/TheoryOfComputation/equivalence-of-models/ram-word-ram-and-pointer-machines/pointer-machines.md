# Pointer machines (Tarjan)

A **pointer machine** has finitely many registers and an expandable pool of records, all with the same finite list of fields; registers and fields hold either pointers to records (or null) or data values from a fixed data model. The instructions create a new record, copy pointers or data between registers and fields of the record pointed to by a register, compare pointers for equality, apply the model's operations and tests to data, and branch. Memory is reached only by following pointers: no arithmetic on pointers is allowed. Running time is the number of instructions executed.

## Depends on

- [Output of a RAM machine](../random-access-machines/ram-eval.md)

## Sources

- Robert Endre Tarjan, "A Class of Algorithms Which Require Nonlinear Time to Maintain Disjoint Sets", Journal of Computer and System Sciences 18(2), 1979, Section 2.
