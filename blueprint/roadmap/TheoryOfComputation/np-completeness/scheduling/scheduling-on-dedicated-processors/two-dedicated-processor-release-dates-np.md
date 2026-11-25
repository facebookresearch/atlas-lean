# TWO DEDICATED PROCESSORS WITH RELEASE DATES `P2|r_i;fix_i|Cmax` is NP-complete

The TWO DEDICATED PROCESSORS WITH RELEASE DATES `P2|r_i;fix_i|Cmax` decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: two processors `M₁`, `M₂`, each executing at most one task at a time; `n` tasks, task `i` with a processing time `p_i ∈ ℤ⁺`, a nonempty set `fix_i ⊆ {M₁, M₂}` of processors that it uses simultaneously during its whole (uninterrupted) processing, and a release date `r_i ∈ ℤ₀⁺` before which it cannot start; and a bound `K`. Tasks whose processor sets intersect cannot overlap in time. Question: is there a schedule with makespan `max_i C_i ≤ K`, where `C_i` is the completion time of task `i`?

## Sources

- J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272, doi:10.1016/0166-218X(94)90012-4, Theorem 2.8.
- P. Brucker and S. Knust, *Complexity results for scheduling problems*, http://www2.informatik.uni-osnabrueck.de/knust/class/, class `mpt` (multiprocessor tasks), entry `P2|r_i;fix_i|C_max` (minimal NP-hard in the strong sense, citing Hoogeveen et al. 1994).
