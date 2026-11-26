# An ordinal map reads edge labels or inserts one

Let A be a type with an element 1, let f : X ⟶ Y be a simplex-category morphism and let a :
Fin Y.len → A label the target edges. For i : Fin X.len, pullbackEdges f a i is a(f(i)) if
f(i) < f(i + 1), and is 1 otherwise. Here i and i + 1 are the endpoints i.castSucc and i.succ,
and the strict inequality ensures that f(i) is a valid target edge index.
