/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.DirichletCharacters

namespace CharacterGroup

variable {G : Type*} [CommGroup G] [Fintype G]

noncomputable instance instFintype : Fintype (CharacterGroup G) := Fintype.ofFinite _

noncomputable def doubleDualEquiv : G ≃* CharacterGroup (CharacterGroup G) :=
  (CommGroup.monoidHomMonoidHomEquiv G ℂ).symm

end CharacterGroup
