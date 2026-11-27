# Deleting an entry from the list of a finite tuple

For `v : Fin (n + 1) → α`, deleting list position `i.val` from `List.ofFn v`
gives `List.ofFn (i.removeNth v)`, preserving the order of the other entries.
No structure on the entry type `α` is required.
