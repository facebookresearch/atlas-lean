# Splitting a list at the occurrences of a root

For a set $E$ and $e \in E$, the splitting of a list is defined recursively: the empty list splits into no pieces; a list $(x, r_1, \dots, r_k)$ in which no $r_i$ equals $e$ is a single piece; otherwise, if $r_j$ is the first entry of $(r_1, \dots, r_k)$ equal to $e$, the first piece is $(x, r_1, \dots, r_j)$ and the remaining pieces are the splitting of $(r_j, r_{j+1}, \dots, r_k)$. Consecutive pieces share the occurrence of $e$ at which they meet.
