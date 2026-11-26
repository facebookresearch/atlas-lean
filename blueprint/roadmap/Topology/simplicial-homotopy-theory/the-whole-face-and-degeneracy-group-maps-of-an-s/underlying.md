# Underlying simplicial set of a simplicial group

For `G : SimplicialObject GrpCat.{u}`, the simplicial set `underlying G : SSet.{u}` is `G ⋙
forget GrpCat`. At each `n : SimplexCategoryᵒᵖ`, its simplices are the elements of the group
`G.obj n`, and its simplicial operators are the underlying functions of `G.map`.
