/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AptIsCoxeterProof

open ChamberComplex

variable {V : Type*} [DecidableEq V]

namespace ThicknessAptStructure

/-- A chamber of the building that lies in an apartment is also a maximal face
of that apartment. -/
lemma building_max_in_apt_is_apt_max
    {K : ChamberComplex V} {pre : AptIsCoxeterProof.PreApartmentData K}
    {A : SimplicialComplex V} (hA : A ∈ pre.apartments)
    {C : Finset V} (hC_A : C ∈ A.faces) (hC_K : K.toSimplicialComplex.IsMaximal C) :
    A.IsMaximal C :=
  pre.building_maximal_in_apt_is_apt_maximal A hA C hC_A hC_K

/-- A maximal face of an apartment is also a chamber of the ambient building. -/
lemma apt_max_is_building_max
    {K : ChamberComplex V} {pre : AptIsCoxeterProof.PreApartmentData K}
    {A : SimplicialComplex V} (hA : A ∈ pre.apartments)
    {C : Finset V} (hC : A.IsMaximal C) :
    K.toSimplicialComplex.IsMaximal C :=
  pre.maximal_in_apt_is_maximal A hA C hC

end ThicknessAptStructure
