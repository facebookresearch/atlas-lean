# Simplicial operators preserve group multiplication

For `G : SimplicialObject GrpCat.{u}`, an arrow `α : n ⟶ m` in `SimplexCategoryᵒᵖ`, and `x, y ∈ (underlying G).obj n`,
`(underlying G).map α (x * y) = (underlying G).map α x * (underlying G).map α y`.
This is the multiplicativity of the group homomorphism `G.map α`.
