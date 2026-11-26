# A semisimplicial homotopy is endpoint and face data

For semisimplicial morphisms f, g : X ⟶ Y in a category C, a homotopy consists of maps h_i^(n)
: X_n ⟶ Y_(n+1), indexed by i : Fin (n + 1). Its endpoints are h₀^(n) ≫ Y.δ 0 = g_n and
h_(Fin.last n)^(n) ≫ Y.δ (Fin.last (n + 1)) = f_n.

For i : Fin (n + 2) and j : Fin (n + 1), the face conditions are h_(j.succ)^(n+1) ≫ Y.δ
i.castSucc = X.δ i ≫ h_j^(n) when i ≤ j.castSucc, and h_(j.castSucc)^(n+1) ≫ Y.δ i.succ = X.δ
i ≫ h_j^(n) when j.castSucc < i. The remaining adjacent relation is h_(j.succ)^(n+1) ≫ Y.δ
j.castSucc.succ = h_(j.castSucc)^(n+1) ≫ Y.δ j.castSucc.succ.
