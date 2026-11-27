# Leaves below the lowest common ancestor

For a rooted binary tree $T$ with labeled leaves and labels $i$, $j$, descending from the root into a child (the left child first) as long as that child has both $i$ and $j$ among its leaves, the count $|\mathrm{leaves}(T[i \vee j])|$ is the number of leaves of the subtree where the descent stops ($1$ at a single leaf, and $|\mathrm{leaves}(T)|$ when no proper child subtree contains both). When the leaf labels of $T$ are distinct, this is the number of leaves of the smallest subtree of $T$ containing both $i$ and $j$ among its leaves.
