# Gentle measurement lemma

Let $\rho$ be a density operator and $0 \preceq E \preceq I$ with $\mathrm{Tr}(E\rho) \ge 1 - \eta$. Then

$$
\left\| \rho - \frac{\sqrt E \rho \sqrt E}{\mathrm{Tr}(E\rho)} \right\|_1 \le 2\sqrt{\eta} .
$$

## Proof sketch

For a pure state $|\psi\rangle$ the post-measurement state $\sqrt E|\psi\rangle/\|\sqrt E\psi\|$ has overlap $\langle\psi|\sqrt E|\psi\rangle/\sqrt{\langle\psi|E|\psi\rangle} \ge \sqrt{\langle \psi | E | \psi\rangle} \ge \sqrt{1-\eta}$ with $|\psi\rangle$ since $\sqrt E \succeq E$, and the trace distance of pure states is $2\sqrt{1 - |\langle\cdot|\cdot\rangle|^2} \le 2\sqrt\eta$. The mixed case follows from purification and monotonicity of trace distance.

## Depends on

- [Trace distance: metric, operational form and contractivity](../remaining-clauses-of-trace-distance-and-contractivity.md)

## Sources

- Andreas Winter, "Coding theorem and strong converse for quantum channels", IEEE Transactions on Information Theory 45(7) (1999).
- Scott Aaronson, "Shadow tomography of quantum states", STOC (2018), SIAM Journal on Computing 49(5) (2020); arXiv:1711.01053.
