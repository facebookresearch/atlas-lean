# Ilango–Li–Williams: under subexponentially secure iO, deterministic polynomial-time Avoid implies NP = coNP

Assume subexponentially secure indistinguishability obfuscation exists. If Avoid has a deterministic polynomial-time algorithm then $\mathrm{NP}=\mathrm{coNP}$. Hardness of Avoid also follows from polynomially secure iO together with a weaker variant of the Nondeterministic Exponential Time Hypothesis.

Moreover, assuming subexponentially secure iO and that $\mathrm{coNP}$ is not infinitely often in $\mathrm{AM}$, Avoid has no deterministic polynomial-time algorithm even with $O(1)$ queries to an oracle that inverts the input circuit on chosen $m$-bit strings. Consequently the dual weak pigeonhole principle is not provable in Cook's theory $\mathrm{PV}_1$, separating $\mathrm{PV}_1$ from Jeřábek's theory $\mathrm{APC}_1$ under these assumptions.

## Proof sketch

From an instance of a $\mathrm{coNP}$-complete problem one builds expanding circuits by obfuscating programs whose functionality depends on the instance only through properties iO hides; since a deterministic Avoid algorithm must output a fixed non-image of each obfuscated circuit, iO security turns that output into a short certificate, placing the problem in $\mathrm{NP}$. The bounded-arithmetic separation uses the witnessing theorem for $\mathrm{PV}_1$, which turns a proof of the principle into such an oracle algorithm.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)
- [Indistinguishability and virtual black-box obfuscation](../../../../ComputerScience/cryptography/program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Sources

- Rahul Ilango, Jiatu Li and Ryan Williams, "Indistinguishability Obfuscation, Range Avoidance, and Bounded Arithmetic", STOC (2023), ECCC TR23-038.
