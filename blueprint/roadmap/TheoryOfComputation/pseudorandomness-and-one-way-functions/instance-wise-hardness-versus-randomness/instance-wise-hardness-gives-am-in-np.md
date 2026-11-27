# van Melkebeek–Sdroievski: instance-wise hardness for Arthur–Merlin protocols gives AM ⊆ NP

Let $f\colon\{0,1\}^n\to\{0,1\}^n$ be a length-preserving function computable by a single-valued nondeterministic algorithm running in time $n^{a}$. If every Arthur–Merlin protocol running in time $n^{c}$, for a suitable $c=O(\log^2 a)$, computes $f$ correctly on only finitely many inputs, then $\mathrm{AM}\subseteq\mathrm{NP}$.

In the converse direction, constructive lower bounds against Arthur–Merlin protocols that go through a compression phase are equivalent to derandomization of $\mathrm{AM}$ via targeted hitting-set generators.

## Proof sketch

The Chen–Tell layered arithmetization is replaced by probabilistically checkable proofs for the nondeterministic computation of $f(x)$: Merlin supplies the PCP, and the targeted hitting-set generator is built from the input $x$ and PCP encodings. A test that avoids the generator lets an Arthur–Merlin protocol reconstruct $f(x)$ instance-wise, using Merlin to supply and Arthur to spot-check the needed proof values, contradicting the almost-all-inputs hardness.

## Depends on

- [The class $\mathsf{AM}$ (Arthur–Merlin)](../../complexity-classes/time-and-space-complexity-classes/am.md)
- [Hardness of a multi-output function on almost all inputs for probabilistic time](almost-all-inputs-hardness.md)
- [Targeted pseudorandom generators and targeted hitting-set generators](targeted-prg-and-targeted-hsg.md)

## Proof depends on

- [Chen–Tell instance-wise reconstruction: a targeted HSG from a shallow logspace-uniform circuit](instance-wise-reconstruction-targeted-hsg.md)

## Sources

- Dieter van Melkebeek and Nicollas Mocelin Sdroievski, "Instance-Wise Hardness versus Randomness Tradeoffs for Arthur-Merlin Protocols", CCC (2023), ECCC TR23-029.
- Dieter van Melkebeek and Nicollas Mocelin Sdroievski, "Instance-Wise Hardness and Refutation versus Derandomization for Arthur-Merlin Protocols", Computational Complexity 34 (2025).
