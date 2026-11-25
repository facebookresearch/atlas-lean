# Deterministic polynomial identity testing

Can one deterministically decide in polynomial time whether a general commutative arithmetic circuit computes the zero polynomial? This is a central derandomization target.

## What would settle it

Define circuit syntax and polynomial semantics, including constant encodings. Construct a deterministic decider and prove both semantic correctness and polynomial bit complexity, or establish an appropriately scoped impossibility result. Black-box and white-box versions must be distinguished.

## Status

The cited sources, in the versions cited, record the partial results below; they do not pose the question in this form, and this page does not certify its present status.

Kabanets and Impagliazzo prove that a deterministic polynomial-time (or nondeterministic subexponential-time) identity test implies circuit lower bounds, either NEXP ⊄ P/poly or a superpolynomial arithmetic circuit lower bound for the permanent. Deterministic tests for restricted circuit classes do not solve the general case.

This page records the research target above and asserts no theorem or present-status certification.

## Sources

- V. Kabanets and R. Impagliazzo, *Derandomizing polynomial identity tests means proving circuit lower bounds*, Computational Complexity 13 (2004), abstract. <https://www.cs.sfu.ca/~kabanets/Research/poly.html>
- Nikolai Chukhin et al., *A Little Derandomization Goes a Long Way: Unconditional Circuit Lower Bounds using Low-Degree PIT*, arXiv:2611.07972v1 (2026), abstract. <https://arxiv.org/abs/2611.07972v1>
