# Homogeneous depth-four circuits with bounded bottom fan-in

Let $\mathbb{F}$ be a field. A **$\Sigma\Pi^{[a]}\Sigma\Pi^{[t]}$ circuit** of size $s$ computes a polynomial of the form

$$
C(x) = \sum_{i=1}^{s} \prod_{j=1}^{a_i} Q_{i,j}(x), \qquad a_i \le a,\ \deg Q_{i,j} \le t,
$$

where each $Q_{i,j}$ is given as a sum of monomials and $s$ bounds the total number of monomials and gates. The circuit is **homogeneous** if every $Q_{i,j}$ is homogeneous and every product $\prod_j Q_{i,j}$ has the same degree $d$. A **$\Sigma\Pi\Sigma$ circuit** (depth three) is the case $t = 1$, i.e. a sum of products of affine linear forms; its **top fan-in** is $s$ and its **formal degree** is $\max_i a_i$.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Sources

- M. Agrawal, V. Vinay, "Arithmetic circuits: a chasm at depth four", FOCS (2008).
- A. Gupta, P. Kamath, N. Kayal, R. Saptharishi, "Approaching the chasm at depth four", Journal of the ACM 61 (2014); CCC (2013).
- R. Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", version 9 (2021), github survey.
