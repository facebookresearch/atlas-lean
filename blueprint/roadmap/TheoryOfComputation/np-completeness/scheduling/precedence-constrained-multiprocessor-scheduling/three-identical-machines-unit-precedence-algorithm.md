# Unit-time precedence scheduling on three identical machines

Consider $n\ge1$ jobs and an acyclic list of directed precedence pairs. A schedule with horizon $T$ assigns a time slot $\tau(v)\in[1,T]$ to every job, uses at most three jobs per slot, and requires $\tau(u)<\tau(v)$ for every precedence pair $(u,v)$. One finite deterministic multitape machine takes this instance with an optional deadline. With no deadline, it returns a slot list for a smallest feasible $T$. For a supplied deadline $1\le T\le n$, it returns a feasible slot list for $T$ if one exists and the absence flag otherwise. The no-deadline branch returns the slot list, not a separate makespan field.

The input begins with the absent/present bit and optional encoded deadline, then gives a length-prefixed list of all one-based job names and a length-prefixed list of one-based endpoint pairs. Naturals use canonical little-endian binary digits (empty at zero), prefixed by as many ones as there are digits and then a zero. An answer is an absence bit or a presence bit and the length-prefixed list of encoded slots in job order. For some positive natural $C$, the machine halts with exactly the encoded answer on the right part of tape zero, starting at its current head, within $C(L+2)^{150020}$ steps for input bit length $L$. The machine uses finite alphabets and control, starts in state zero, and can write and move left, right or stay on each tape at one step.

## Depends on

- [Precedence-constrained scheduling feasibility](precedence-constrained-scheduling-feasib.md) specializes to unit lengths and three identical processors by taking $\tau(v)=\sigma(v)+1$ for the start times $\sigma$. The acyclic edge list, output requirements and machine code are as above.

## Proof depends on

- A complete precedence scheduling algorithm on three identical machines, the minimum-horizon search, and a bit-time compilation with the specified fixed exponent covering both branches.

## Expansion

Prove equivalence of at most three jobs per slot with explicit identical processor assignments; isolate acyclic edge-list semantics and binary I/O. Keep the valid-deadline restriction and the literal exponent when transporting to a canonical machine.

## Sources

- OpenAI, [ThreeMachine.lean, instance, machine and `ReleaseTheorem`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThreeMachine.lean#L7-L96).
