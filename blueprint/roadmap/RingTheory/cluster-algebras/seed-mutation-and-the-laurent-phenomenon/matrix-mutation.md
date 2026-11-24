# Matrix mutation

The mutation of an integer square matrix $B = (b_{ij})$ in direction $k$ is the matrix
$\mu_k(B) = (b'_{ij})$ with

$$b'_{ij} = \begin{cases} -b_{ij} & \text{if } i = k \text{ or } j = k, \\ b_{ij} + b_{ik} b_{kj} & \text{if } b_{ik} > 0 \text{ and } b_{kj} > 0, \\ b_{ij} - b_{ik} b_{kj} & \text{if } b_{ik} < 0 \text{ and } b_{kj} < 0, \\ b_{ij} & \text{otherwise} \end{cases}$$

(Fomin, Williams and Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*,
arXiv:1608.05735v5, Lemma 2.7.3, equation (2.7.1), and Definition 2.7.6, square case $m = n$).
