/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CompositionSeries
import Atlas.LieGroups.code.DualityFunctorDefs

noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def HasStandardFiltration
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (V : Type uCatO) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (_hV : IsCategoryO Δ rd V) : Prop :=
  ∃ (n : ℕ) (F : Fin (n + 1) → LieSubmodule R 𝔤 V),
    F ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
    F ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤ ∧
    (∀ i : Fin n, F i.castSucc < F i.succ) ∧


    (∀ i : Fin n, ∃ (lam_i : Δ.𝔥 →ₗ[R] R)
      (Q : Type uCatO) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : LieRingModule 𝔤 Q) (_ : LieModule R 𝔤 Q)
      (_ : IsVermaModule Δ Q lam_i)
      (π : ↥(F i.succ) →ₗ⁅R, 𝔤⁆ Q),
      Function.Surjective π ∧
      (∀ x : ↥(F i.succ), π x = 0 ↔ (x : V) ∈ F i.castSucc))

def Ext1VanishingForContragredientVerma
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (X : Type uCatO) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X) : Prop :=
  ∀ (lam : Δ.𝔥 →ₗ[R] R)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (hMlamDualO : IsCategoryO Δ rd MlamDual)
    (_hContra : IsContragredientVerma rd MlamDual lam hMlamDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (i : MlamDual →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective i)
    (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)

    (_hexact : ∀ e : E, p e = 0 ↔ ∃ m : MlamDual, i m = e),
    ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x






























theorem standard_filtration_gluing
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)

    (Z : LieSubmodule R 𝔤 X)
    (lam : Δ.𝔥 →ₗ[R] R)
    (Q : Type uCatO) [AddCommGroup Q] [Module R Q]
    [LieRingModule 𝔤 Q] [LieModule R 𝔤 Q]
    (_ : IsVermaModule Δ Q lam)
    (π : ↥Z →ₗ⁅R, 𝔤⁆ Q)
    (hπ_surj : Function.Surjective π)
    (hπ_ker : ∀ x : ↥Z, π x = 0 ↔ (x : X) ∈ (⊥ : LieSubmodule R 𝔤 X))

    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hYO : IsCategoryO Δ rd Y)
    (q : X →ₗ⁅R, 𝔤⁆ Y)
    (hq_surj : Function.Surjective q)
    (hq_ker : ∀ x : X, q x = 0 ↔ x ∈ Z)

    (hY_sf : HasStandardFiltration rd Y hYO) :
    HasStandardFiltration rd X hXO := by

  obtain ⟨n, G, hG_bot, hG_top, hG_strict, hG_verma⟩ := hY_sf

  have hcomap_bot : LieSubmodule.comap q ⊥ = Z := by
    ext x; simp only [LieSubmodule.mem_comap, LieSubmodule.mem_bot]; exact hq_ker x

  have hcomap_top : LieSubmodule.comap q ⊤ = ⊤ := by
    ext x; simp [LieSubmodule.mem_comap]

  have hcomap_G0 : LieSubmodule.comap q (G ⟨0, Nat.zero_lt_succ n⟩) = Z := by
    rw [hG_bot]; exact hcomap_bot

  have hcomap_Gn : LieSubmodule.comap q (G ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩) = ⊤ := by
    rw [hG_top]; exact hcomap_top

  have hcomap_strict : StrictMono (LieSubmodule.comap (f := q)) := by
    intro A B hAB
    refine lt_of_le_of_ne ((LieSubmodule.gc_map_comap q).monotone_u hAB.le) ?_
    intro heq
    have h_surj_map : ∀ N', LieSubmodule.map q (LieSubmodule.comap q N') = N' := by
      intro N'
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact LieSubmodule.mem_comap.mp hx
      · intro hy; obtain ⟨x, rfl⟩ := hq_surj y; exact ⟨x, LieSubmodule.mem_comap.mpr hy, rfl⟩
    have := congr_arg (LieSubmodule.map q) heq
    rw [h_surj_map, h_surj_map] at this
    exact (ne_of_lt hAB) this


  let F : Fin (n + 1 + 1) → LieSubmodule R 𝔤 X := fun ⟨k, hk⟩ =>
    if hk0 : k = 0 then ⊥
    else LieSubmodule.comap q (G ⟨k - 1, by omega⟩)

  have hF_bot : F ⟨0, Nat.zero_lt_succ (n + 1)⟩ = ⊥ := by
    simp only [F, dif_pos rfl]

  have hF_top : F ⟨n + 1, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤ := by
    simp only [F, dif_neg (Nat.succ_ne_zero n)]
    simp only [show n + 1 - 1 = n from rfl]
    exact hcomap_Gn

  have hF_strict : ∀ i : Fin (n + 1), F i.castSucc < F i.succ := by
    intro ⟨i, hi⟩

    simp only [Fin.castSucc_mk, Fin.succ_mk, F]

    simp only [dif_neg (Nat.succ_ne_zero i)]
    simp only [show i + 1 - 1 = i from rfl]
    by_cases hi0 : i = 0
    ·
      subst hi0
      show ⊥ < LieSubmodule.comap q (G ⟨0, _⟩)
      rw [bot_lt_iff_ne_bot, hcomap_G0]

      intro hZ_bot
      have hVerma := ‹IsVermaModule Δ Q lam›
      obtain ⟨z, hz⟩ := hπ_surj hVerma.highestWeightVec
      have : (z : X) ∈ (⊥ : LieSubmodule R 𝔤 X) := hZ_bot ▸ z.2
      have : π z = 0 := (hπ_ker z).mpr this
      exact hVerma.hwv_ne_zero (hz ▸ this)

    ·
      simp only [dif_neg hi0]
      apply hcomap_strict
      have hi' : i - 1 < n := by omega
      have := hG_strict ⟨i - 1, hi'⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at this
      convert this using 1
      exact congr_arg G (Fin.ext (by simp; omega))


  have hF_verma : ∀ i : Fin (n + 1), ∃ (lam_i : Δ.𝔥 →ₗ[R] R)
      (Q_i : Type uCatO) (_ : AddCommGroup Q_i) (_ : Module R Q_i)
      (_ : LieRingModule 𝔤 Q_i) (_ : LieModule R 𝔤 Q_i)
      (_ : IsVermaModule Δ Q_i lam_i)
      (π_i : ↥(F i.succ) →ₗ⁅R, 𝔤⁆ Q_i),
      Function.Surjective π_i ∧
      (∀ x : ↥(F i.succ), π_i x = 0 ↔ (x : X) ∈ F i.castSucc) := by
    intro ⟨i, hi⟩
    by_cases hi0 : i = 0
    ·
      subst hi0
      have hF1_eq : F ⟨1, by omega⟩ = Z := by
        simp only [F, dif_neg one_ne_zero]
        simp only [show 1 - 1 = 0 from rfl]
        exact hcomap_G0

      have hF1_le_Z : F ⟨1, by omega⟩ ≤ Z := hF1_eq ▸ le_refl _
      have hZ_le_F1 : Z ≤ F ⟨1, by omega⟩ := hF1_eq ▸ le_refl _

      let π₀ : ↥(F ⟨1, by omega⟩) →ₗ⁅R, 𝔤⁆ Q :=
        { toFun := fun x => π ⟨x.1, hF1_le_Z x.2⟩
          map_add' := fun a b => by
            have : (⟨(a + b).1, hF1_le_Z (a + b).2⟩ : ↥Z) =
                ⟨a.1, hF1_le_Z a.2⟩ + ⟨b.1, hF1_le_Z b.2⟩ := Subtype.ext rfl
            simp only [this, map_add]
          map_smul' := fun r x => by
            have : (⟨(r • x).1, hF1_le_Z (r • x).2⟩ : ↥Z) =
                r • ⟨x.1, hF1_le_Z x.2⟩ := Subtype.ext rfl
            simp only [this, map_smul, RingHom.id_apply]
          map_lie' := fun {g x} => by
            have : (⟨(⁅g, x⁆ : ↥(F ⟨1, by omega⟩)).1, hF1_le_Z (⁅g, x⁆ : ↥(F ⟨1, by omega⟩)).2⟩ : ↥Z) =
                ⁅g, (⟨x.1, hF1_le_Z x.2⟩ : ↥Z)⁆ := Subtype.ext rfl
            simp only [this, LieModuleHom.map_lie] }
      refine ⟨lam, Q, inferInstance, inferInstance, inferInstance, inferInstance,
        ‹IsVermaModule Δ Q lam›, π₀, ?_, ?_⟩
      ·
        intro y
        obtain ⟨z, hz⟩ := hπ_surj y
        exact ⟨⟨z.1, hZ_le_F1 z.2⟩, hz⟩
      ·
        intro x
        show π ⟨x.1, hF1_le_Z x.2⟩ = 0 ↔ (x : X) ∈ F ⟨0, by omega⟩
        rw [hF_bot, hπ_ker]
    ·
      have hi1 : i - 1 < n := by omega
      obtain ⟨lam_j, Q_j, instQa, instQb, instQc, instQd, hVerma_j, π_j,
              hπj_surj, hπj_ker⟩ := hG_verma ⟨i - 1, hi1⟩
      letI := instQa; letI := instQb; letI := instQc; letI := instQd

      have hFsucc : F ⟨i + 1, by omega⟩ =
          LieSubmodule.comap q (G (⟨i - 1, hi1⟩ : Fin n).succ) := by
        simp only [F, dif_neg (Nat.succ_ne_zero i)]
        exact congr_arg (LieSubmodule.comap q) (congr_arg G (Fin.ext (by simp [Fin.succ_mk]; omega)))

      have hFcast : F ⟨i, by omega⟩ =
          LieSubmodule.comap q (G (⟨i - 1, hi1⟩ : Fin n).castSucc) := by
        simp only [F, dif_neg hi0, Fin.castSucc_mk]

      have hFsucc_le : F ⟨i + 1, by omega⟩ ≤
          LieSubmodule.comap q (G (⟨i - 1, hi1⟩ : Fin n).succ) := hFsucc ▸ le_refl _

      let πComp : ↥(F ⟨i + 1, by omega⟩) →ₗ⁅R, 𝔤⁆ Q_j :=
        { toFun := fun x =>
            π_j ⟨q x.1, LieSubmodule.mem_comap.mp (hFsucc_le x.2)⟩
          map_add' := fun a b => by
            have h1 : (⟨q (a + b).1, LieSubmodule.mem_comap.mp (hFsucc_le (a + b).2)⟩ :
                ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) =
                ⟨q a.1, LieSubmodule.mem_comap.mp (hFsucc_le a.2)⟩ +
                ⟨q b.1, LieSubmodule.mem_comap.mp (hFsucc_le b.2)⟩ :=
              Subtype.ext (map_add q a.1 b.1)
            simp only [h1, map_add]
          map_smul' := fun r x => by
            have h1 : (⟨q (r • x).1, LieSubmodule.mem_comap.mp (hFsucc_le (r • x).2)⟩ :
                ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) =
                r • ⟨q x.1, LieSubmodule.mem_comap.mp (hFsucc_le x.2)⟩ :=
              Subtype.ext (map_smul q r x.1)
            simp only [h1, map_smul, RingHom.id_apply]
          map_lie' := fun {g x} => by
            have h1 : (⟨q (⁅g, x⁆ : ↥(F ⟨i + 1, by omega⟩)).1,
                LieSubmodule.mem_comap.mp (hFsucc_le (⁅g, x⁆ : ↥(F ⟨i + 1, by omega⟩)).2)⟩ :
                ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) =
                ⁅g, (⟨q x.1, LieSubmodule.mem_comap.mp (hFsucc_le x.2)⟩ :
                  ↥(G (⟨i - 1, hi1⟩ : Fin n).succ))⁆ :=
              Subtype.ext (LieModuleHom.map_lie q g x.1)
            simp only [h1, LieModuleHom.map_lie] }
      refine ⟨lam_j, Q_j, instQa, instQb, instQc, instQd, hVerma_j, πComp, ?_, ?_⟩
      ·
        intro y
        obtain ⟨g, hg⟩ := hπj_surj y
        obtain ⟨x, hx⟩ := hq_surj (g : Y)
        have hx_mem : x ∈ F ⟨i + 1, by omega⟩ := by
          rw [hFsucc]; exact LieSubmodule.mem_comap.mpr (hx ▸ g.2)
        refine ⟨⟨x, hx_mem⟩, ?_⟩
        show π_j ⟨q x, LieSubmodule.mem_comap.mp (hFsucc_le hx_mem)⟩ = y
        have hqx_eq : (⟨q x, LieSubmodule.mem_comap.mp (hFsucc_le hx_mem)⟩ :
            ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) = g :=
          Subtype.ext hx
        rw [hqx_eq, hg]
      ·
        intro x
        show π_j ⟨q x.1, _⟩ = 0 ↔ (x : X) ∈ F ⟨i, by omega⟩
        rw [hπj_ker, hFcast]
        simp [LieSubmodule.mem_comap]

  exact ⟨n + 1, F, hF_bot, hF_top, hF_strict, hF_verma⟩



lemma UEA_induction_on_gen
    {R : Type*} [CommRing R]
    {L : Type*} [LieRing L] [LieAlgebra R L]
    {C : UniversalEnvelopingAlgebra R L → Prop}
    (u : UniversalEnvelopingAlgebra R L)
    (h_alg : ∀ r : R, C (algebraMap R _ r))
    (h_ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
    (h_mul : ∀ a b, C a → C b → C (a * b))
    (h_add : ∀ a b, C a → C b → C (a + b)) :
    C u := by
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R L) u
  change C ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact h_alg r
  | ι x => exact h_ι x
  | mul a b ha hb => rw [map_mul]; exact h_mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact h_add _ _ ha hb


lemma lieModuleHom_ueaSubalg_compat_gen
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N)
    (u : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    f ((ueaSubalgAction Δ.𝔫_neg M u) m) = (ueaSubalgAction Δ.𝔫_neg N u) (f m) := by
  suffices h : ∀ m, f ((ueaSubalgAction Δ.𝔫_neg M u) m) =
      (ueaSubalgAction Δ.𝔫_neg N u) (f m) from h m
  induction u using UEA_induction_on_gen with
  | h_alg r =>
    intro m
    simp only [ueaSubalgAction, Algebra.algebraMap_eq_smul_one]
    simp [LinearMap.smul_apply, map_smul]
  | h_ι x =>
    intro m
    simp only [ueaSubalgAction, UniversalEnvelopingAlgebra.lift_ι_apply,
      LieModule.toEnd_apply_apply]
    exact f.map_lie x m
  | h_mul a b ha hb =>
    intro m
    simp only [map_mul]
    change f ((ueaSubalgAction Δ.𝔫_neg M a).comp (ueaSubalgAction Δ.𝔫_neg M b) m) =
           (ueaSubalgAction Δ.𝔫_neg N a).comp (ueaSubalgAction Δ.𝔫_neg N b) (f m)
    simp only [LinearMap.comp_apply]
    rw [ha ((ueaSubalgAction Δ.𝔫_neg M b) m)]
    congr 1
    exact hb m
  | h_add a b ha hb =>
    intro m
    simp only [map_add, LinearMap.add_apply, map_add]
    rw [ha m, hb m]


lemma Module.Free.of_right_split_ses
    {S : Type*} [Ring S]
    {A M B : Type*} [AddCommGroup A] [AddCommGroup M] [AddCommGroup B]
    [Module S A] [Module S M] [Module S B]
    (j : A →ₗ[S] M) (g : M →ₗ[S] B) (s : B →ₗ[S] M)
    (hj_inj : Function.Injective j)
    (hexact : LinearMap.range j = LinearMap.ker g)
    (hgs : g.comp s = LinearMap.id)
    (hA : Module.Free S A) (hB : Module.Free S B) :
    Module.Free S M := by
  haveI := hA; haveI := hB
  let φ : A × B →ₗ[S] M := j.coprod s
  have hg_j : ∀ a, g (j a) = 0 := by
    intro a
    have : j a ∈ LinearMap.range j := ⟨a, rfl⟩
    rw [hexact] at this; exact this
  have hg_s : ∀ b, g (s b) = b := fun b => LinearMap.ext_iff.mp hgs b
  have φ_bij : Function.Bijective φ := by
    constructor
    · intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
      have h' : j a₁ + s b₁ = j a₂ + s b₂ := h
      have hg1 : g (j a₁ + s b₁) = g (j a₂ + s b₂) := congr_arg g h'
      rw [map_add, map_add, hg_j, hg_j, zero_add, zero_add, hg_s, hg_s] at hg1
      subst hg1
      have hja : j a₁ = j a₂ := by rwa [add_right_cancel_iff] at h'
      exact Prod.ext (hj_inj hja) rfl
    · intro m
      have hmsg : m - s (g m) ∈ LinearMap.ker g := by
        rw [LinearMap.mem_ker, map_sub, hg_s, sub_self]
      rw [← hexact] at hmsg
      obtain ⟨a, ha⟩ := hmsg
      exact ⟨⟨a, g m⟩, show j a + s (g m) = m from by rw [ha, sub_add_cancel]⟩
  exact Module.Free.of_equiv' (Module.Free.prod S A B)
    (LinearEquiv.ofBijective φ φ_bij)


noncomputable def lieModuleHomToUEALinearMap_gen
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {N : Type*} [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    letI := instModuleUEASubalg Δ.𝔫_neg N
    M →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] N := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  letI := instModuleUEASubalg Δ.𝔫_neg N
  exact {
    toFun := f
    map_add' := f.toLinearMap.map_add
    map_smul' := fun r m => lieModuleHom_ueaSubalg_compat_gen f r m

  }



lemma UEA_induction_on_local
    {R : Type*} [CommRing R]
    {L : Type*} [LieRing L] [LieAlgebra R L]
    {C : UniversalEnvelopingAlgebra R L → Prop}
    (u : UniversalEnvelopingAlgebra R L)
    (h_alg : ∀ r : R, C (algebraMap R _ r))
    (h_ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
    (h_mul : ∀ a b, C a → C b → C (a * b))
    (h_add : ∀ a b, C a → C b → C (a + b)) :
    C u := by
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R L) u
  change C ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact h_alg r
  | ι x => exact h_ι x
  | mul a b ha hb => rw [map_mul]; exact h_mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact h_add _ _ ha hb


lemma lieModuleHom_ueaSubalg_compat_local
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N)
    (u : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    f ((ueaSubalgAction Δ.𝔫_neg M u) m) = (ueaSubalgAction Δ.𝔫_neg N u) (f m) := by
  suffices h : ∀ m, f ((ueaSubalgAction Δ.𝔫_neg M u) m) =
      (ueaSubalgAction Δ.𝔫_neg N u) (f m) from h m
  induction u using UEA_induction_on_local with
  | h_alg r =>
    intro m
    simp only [ueaSubalgAction, Algebra.algebraMap_eq_smul_one]
    simp [LinearMap.smul_apply, map_smul]
  | h_ι x =>
    intro m
    simp only [ueaSubalgAction, UniversalEnvelopingAlgebra.lift_ι_apply,
      LieModule.toEnd_apply_apply]
    exact f.map_lie x m
  | h_mul a b ha hb =>
    intro m
    simp only [map_mul]
    change f ((ueaSubalgAction Δ.𝔫_neg M a).comp (ueaSubalgAction Δ.𝔫_neg M b) m) =
           (ueaSubalgAction Δ.𝔫_neg N a).comp (ueaSubalgAction Δ.𝔫_neg N b) (f m)
    simp only [LinearMap.comp_apply]
    rw [ha ((ueaSubalgAction Δ.𝔫_neg M b) m)]
    congr 1
    exact hb m
  | h_add a b ha hb =>
    intro m
    simp only [map_add, LinearMap.add_apply, map_add]
    rw [ha m, hb m]


noncomputable def lieModuleHomToUEALinearMap_local
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M N : Type uCatO} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    letI := instModuleUEASubalg Δ.𝔫_neg N
    M →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] N := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  letI := instModuleUEASubalg Δ.𝔫_neg N
  exact {
    toFun := f
    map_add' := f.toLinearMap.map_add
    map_smul' := fun r m => lieModuleHom_ueaSubalg_compat_local f r m
  }

theorem free_nminus_is_projective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXfree : letI := instModuleUEASubalg Δ.𝔫_neg X;
              Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X) :
    letI := instModuleUEASubalg Δ.𝔫_neg X;
    Module.Projective (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X := by
  letI := instModuleUEASubalg Δ.𝔫_neg X
  haveI := hXfree
  exact Module.Projective.of_free

theorem projective_nminus_gives_section
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    {E : Type uCatO} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (p : E →ₗ⁅R, 𝔤⁆ X) (hp : Function.Surjective p)
    (hXproj : letI := instModuleUEASubalg Δ.𝔫_neg X;
              Module.Projective (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X) :
    letI := instModuleUEASubalg Δ.𝔫_neg X;
    letI := instModuleUEASubalg Δ.𝔫_neg E;
    ∃ (s₀ : X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E),
      ∀ x, p (s₀ x) = x := by
  letI := instModuleUEASubalg Δ.𝔫_neg X
  letI := instModuleUEASubalg Δ.𝔫_neg E
  haveI := hXproj

  let p_U : E →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] X :=
    lieModuleHomToUEALinearMap_local p

  have hp_surj : Function.Surjective p_U := hp
  obtain ⟨s₀, hs₀⟩ := Module.projective_lifting_property p_U LinearMap.id hp_surj
  exact ⟨s₀, fun x => by
    have := LinearMap.ext_iff.mp hs₀ x
    simp [p_U, LinearMap.comp_apply, LinearMap.id_apply] at this
    exact this⟩


















def IsFreeOverNMinus
    {Δ : TriangularDecomposition R 𝔤}
    (X : Type*) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X] : Prop :=
  letI := instModuleUEASubalg Δ.𝔫_neg X
  Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X














lemma lie_hom_preserves_weight_space
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {K : Type*} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    {N : Type*} [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : K →ₗ⁅R, 𝔤⁆ N) (μ : Δ.𝔥 →ₗ[R] R)
    {k : K} (hk : k ∈ WeightSpace Δ K μ) :
    f k ∈ WeightSpace Δ N μ := by
  intro h
  rw [← LieModuleHom.map_lie, hk h, map_smul]

theorem weight_space_sum_disjoint
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Finset (Δ.𝔥 →ₗ[R] R))
    (hlamS : lam ∉ S)
    (v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ)
    (m : M) (hm : m ∈ WeightSpace Δ M lam)
    (hm_sum : m = ∑ μ ∈ S, (v μ : M)) :
    m = 0 := by
  classical

  let w : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ := fun μ =>
    if h : μ = lam then
      ⟨-m, h ▸ (WeightSpace Δ M lam).neg_mem hm⟩
    else
      v μ

  have hsum : ∑ μ ∈ Finset.cons lam S hlamS, (w μ : M) = 0 := by
    rw [Finset.sum_cons]
    simp only [w, dif_pos rfl]
    have hsumS : ∑ μ ∈ S, (w μ : M) = ∑ μ ∈ S, (v μ : M) := by
      apply Finset.sum_congr rfl
      intro μ hμ
      have hne : μ ≠ lam := fun h => hlamS (h ▸ hμ)
      show (w μ : M) = (v μ : M)
      simp only [w, dif_neg hne]
    rw [hsumS, ← hm_sum, neg_add_cancel]

  have hw_lam := weightSpace_sum_eq_zero_components
    (Finset.cons lam S hlamS) w hsum lam (Finset.mem_cons_self lam S)

  simp only [w, dif_pos rfl] at hw_lam
  exact neg_eq_zero.mp hw_lam















end
