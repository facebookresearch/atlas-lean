# Horn-filling simplex from group corrections

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, missing index `i : Fin (n + 3)`, and face
family `h : Fin (n + 3) → (underlying G) _⦋n + 1⦌`, the `(n + 2)`-simplex `hornFiller G i h`
is `upperPass G i h i`. It is obtained by the increasing lower-face pass followed by the
decreasing upper-face pass. When the prescribed faces are compatible away from `i`, it has
each of those faces.
