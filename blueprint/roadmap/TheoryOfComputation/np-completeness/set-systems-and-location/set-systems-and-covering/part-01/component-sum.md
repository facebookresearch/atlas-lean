# Component sum of a partition

For an assignment $f$ of the list positions of $C$ to the parts $0, \dots, K - 1$, the value $\sum_k \max_{j < m} \sum_{v \in C_k} v_j$, where $C_k$ is the sublist of the vectors at the positions $f$ sends to $k$ (positions, not distinct values: a vector listed twice counts twice), entries missing from a vector read as $0$, and the maximum over no coordinates ($m = 0$) is $0$.
