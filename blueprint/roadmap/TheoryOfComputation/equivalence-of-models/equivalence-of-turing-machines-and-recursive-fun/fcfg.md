# Configurations of the wrapped machine

Let $c$ be a partial recursive code, and let
$\Gamma' = \{\mathtt{cons}_l, \mathtt{cons}, \mathtt{bit0}, \mathtt{bit1}\}$ be the alphabet of
Mathlib's multi-stack machine $\mathrm{tr}$ that evaluates such codes. A configuration of the
wrapped machine for $c$ is a configuration of Mathlib's multi-stack (TM2) Turing machine model
with the stack alphabets and labels of the wrapped machine for $c$ and internal states the
optional symbols of $\Gamma'$: it consists of an optional current label (none once the machine
has halted), an internal state that is a symbol of $\Gamma'$ or none, and for each stack $k$ a
finite list of symbols of the alphabet of $k$.
