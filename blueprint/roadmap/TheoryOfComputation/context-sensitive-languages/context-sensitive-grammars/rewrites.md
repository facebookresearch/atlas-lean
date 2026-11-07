# One rewriting step of a grammar

One rewriting step: apply a production in a sentential form
context. This is the generic `Cslib.Decidability.Rewriting.Step` at the
grammar's rules, so grammar derivations reuse the string-rewriting API
instead of a second, incompatible copy of it.
