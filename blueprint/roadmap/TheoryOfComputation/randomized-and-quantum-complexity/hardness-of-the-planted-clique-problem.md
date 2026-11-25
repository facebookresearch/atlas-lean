# Hardness of the planted clique problem

In a uniformly random graph on n vertices (each edge present independently with probability 1/2) a clique of size k is planted. Is there a polynomial-time algorithm that finds the planted clique, or distinguishes the planted graph from a random one, when k ≤ n^{1/2−ε} for a fixed ε > 0?

## What would settle it

Fix the null and planted distributions, the size k = k(n) and the task (search or detection with a stated success probability), and either give a polynomial-time algorithm for k = n^{1/2−ε}, or prove that no polynomial-time algorithm succeeds, which would be a lower bound against all efficient algorithms. Lower bounds for restricted algorithm classes (sum-of-squares, low-degree polynomials, statistical queries) are not lower bounds against every algorithm.

## Status

The cited sources pose this as an open question in the versions cited; this page does not certify its present status. The supporting open-problem statement is older or its status evidence is incomplete; check later literature before relying on it.

Barak, Hopkins, Kelner, Kothari, Moitra and Potechin note that, despite intense effort, the best polynomial-time algorithms only work for cliques of size ε√n, that lower bounds for planted clique are unlikely to follow from conjectured separations such as P ≠ NP because it is an average-case problem, and that the best evidence for its difficulty comes from limitations of particular classes of algorithms; they prove a nearly tight n^{1/2−o(1)} lower bound, with high probability over the random graph, on the value of the degree-d sum-of-squares relaxation for the clique problem when d = o(log n).

This page records the cited research question and asserts no theorem or present-status certification.

## Sources

- B. Barak, S. B. Hopkins, J. Kelner, P. K. Kothari, A. Moitra and A. Potechin, "A nearly tight sum-of-squares lower bound for the planted clique problem", preprint (2016), abstract and introduction. <https://arxiv.org/abs/1604.03084>
