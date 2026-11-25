# Descent of a map into a nerve

For `g : Z ⟶ nerve D`, its
descent `SSet.descNerve g : Z.HomotopyCategory ⥤ D` is the functor
sending a vertex `z` to `CategoryTheory.nerveEquiv (g.app _ z)` and a
generating morphism `SSet.HomotopyCategory.homMk e` to
`CategoryTheory.nerve.homEquiv (e.map g)`.
