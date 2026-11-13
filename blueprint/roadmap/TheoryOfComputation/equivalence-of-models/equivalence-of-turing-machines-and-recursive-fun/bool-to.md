# Bits as stack symbols

Let
$\Gamma' = \{\mathtt{cons}_l, \mathtt{cons}, \mathtt{bit0}, \mathtt{bit1}\}$ be the stack alphabet
of Mathlib's multi-stack machine $\mathrm{tr}$ that evaluates partial recursive codes. This is
the map from bits to $\Gamma'$ that sends $\mathrm{true}$ to $\mathtt{bit1}$ and $\mathrm{false}$
to $\mathtt{bit0}$.
