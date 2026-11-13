# Formula filter of the dense-SAT verifier

The partial map on the work alphabet $G$ that
sends each left symbol $\mathrm{inl}(b)$ to itself and is undefined on every right symbol
$\mathrm{inr}(o)$, including the separator $\mathrm{inr}(\mathrm{none})$, written $\#$.

The verifier's first copying loop uses it, so on the pair encoding of a formula and a
certificate it stops at the separator $\#$.
