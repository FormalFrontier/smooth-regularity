/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SmoothRegularity.CotangentRelationTransport

/-!
# Localized presentation relations in the cotangent complex

This file views presentation relations in the kernel of the presentation
localized at a closed point. It transports the already selected linearly
independent local cotangent classes to the residue-field base change of that
localized extension's cotangent-complex map.

It makes no assertion about the quotient by the selected relations, its
regularity or dimension, or formal smoothness of the target.
-/

public section

open scoped TensorProduct

namespace Algebra.Presentation

universe u v

section LocalizedRelation

variable {K : Type u} [Field K]
variable {S : Type v} [CommRing S] [Algebra K S]

/-- A presentation relation viewed in the kernel of the extension obtained by
localizing at a prime of the target. -/
noncomputable def localizedRelation {n r : ℕ}
    (P : Algebra.Presentation K S (Fin n) (Fin r))
    (m : Ideal S) [m.IsPrime] (j : Fin r) :
    (P.toExtension.localization (S' := Localization.AtPrime m)
      m.primeCompl).ker := by
  let E : Algebra.Extension K (Localization.AtPrime m) :=
    P.toExtension.localization m.primeCompl
  let _ : Algebra P.Ring E.Ring := by
    change Algebra P.Ring
      (Localization (m.primeCompl.comap (algebraMap P.Ring S)))
    infer_instance
  let _ : IsScalarTower P.Ring E.Ring (Localization.AtPrime m) :=
    IsScalarTower.of_algebraMap_eq' <| by
      let N := m.primeCompl.comap (algebraMap P.Ring S)
      let hu : ∀ x : N, IsUnit
          (((algebraMap S (Localization.AtPrime m)).comp
            (algebraMap P.Ring S)) x) :=
        fun x ↦ IsLocalization.map_units (Localization.AtPrime m)
          (⟨algebraMap P.Ring S x, x.2⟩ : m.primeCompl)
      change (algebraMap S (Localization.AtPrime m)).comp
          (algebraMap P.Ring S) =
        (IsLocalization.lift
          (M := N)
          (g := (algebraMap S (Localization.AtPrime m)).comp
            (algebraMap P.Ring S)) hu).comp
          (algebraMap P.Ring (Localization N))
      exact (IsLocalization.lift_comp hu).symm
  exact ⟨algebraMap P.Ring E.Ring (P.relation j), by
    change algebraMap E.Ring (Localization.AtPrime m)
      (algebraMap P.Ring E.Ring (P.relation j)) = 0
    rw [← IsScalarTower.algebraMap_apply]
    change algebraMap S (Localization.AtPrime m)
      (algebraMap P.Ring S (P.relation j)) = 0
    rw [show algebraMap P.Ring S (P.relation j) = 0 from
      P.relation_mem_ker j]
    exact map_zero _⟩

end LocalizedRelation

section CotangentComplex

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {S : Type v} [CommRing S] [Algebra K S] [Algebra.FiniteType K S]

omit [IsAlgClosed K] in
private lemma conormalEquiv_apply {R : Type v}
    [CommRing R] [IsLocalRing R] [Algebra K R]
    (e : IsLocalRing.ResidueField R ≃ₐ[K] K)
    (x : IsLocalRing.maximalIdeal R) :
    IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv e
        ((IsLocalRing.maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1 := by
  exact IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent e x

/-- A fixed family of presentation relations whose literal classes are linearly
independent in the cotangent space of the localized presentation ring remains
linearly independent after mapping into the residue-field base change of the
localized extension's cotangent complex. -/
theorem linearIndependent_localizedCotangentComplex_of_localCotangent
    {n r d : ℕ}
    (P : Algebra.Presentation K S (Fin n) (Fin r))
    (m : Ideal S) [m.IsMaximal]
    (q : Ideal P.toExtension.Ring) [q.IsMaximal]
    (hq : q = m.comap (algebraMap P.toExtension.Ring S))
    (f : Fin d → Fin r)
    (hrel : ∀ i, P.relation (f i) ∈ q)
    (hli : LinearIndependent q.ResidueField (fun i ↦
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)).toCotangent
        ⟨algebraMap P.toExtension.Ring (Localization.AtPrime q)
            (P.relation (f i)),
          (IsLocalization.AtPrime.to_map_mem_maximal_iff
            (Localization.AtPrime q) q (P.relation (f i))).mpr (hrel i)⟩)) :
    let E : Algebra.Extension K (Localization.AtPrime m) :=
      P.toExtension.localization m.primeCompl
    LinearIndependent (IsLocalRing.ResidueField (Localization.AtPrime m))
      (fun i ↦
        (E.cotangentComplex.baseChange
            (IsLocalRing.ResidueField (Localization.AtPrime m)))
          (1 ⊗ₜ[Localization.AtPrime m]
            Algebra.Extension.Cotangent.mk (P.localizedRelation m (f i)))) := by
  subst q
  let q : Ideal P.toExtension.Ring :=
    m.comap (algebraMap P.toExtension.Ring S)
  let rel : Fin d → P.toExtension.Ring := fun i ↦ P.relation (f i)
  have hrel' : ∀ i, rel i ∈ q := hrel
  let E : Algebra.Extension K (Localization.AtPrime m) :=
    P.toExtension.localization m.primeCompl
  let _ : Algebra P.Ring E.Ring := by
    change Algebra P.Ring
      (Localization (m.primeCompl.comap
        (algebraMap P.Ring S)))
    infer_instance
  let _ : IsScalarTower P.Ring E.Ring
      (Localization.AtPrime m) :=
    IsScalarTower.of_algebraMap_eq' <| by
      let N := m.primeCompl.comap (algebraMap P.Ring S)
      let hu : ∀ x : N, IsUnit
          (((algebraMap S (Localization.AtPrime m)).comp
            (algebraMap P.Ring S)) x) :=
        fun x ↦ IsLocalization.map_units (Localization.AtPrime m)
          (⟨algebraMap P.Ring S x, x.2⟩ : m.primeCompl)
      change (algebraMap S (Localization.AtPrime m)).comp
          (algebraMap P.Ring S) =
        (IsLocalization.lift
          (M := N)
          (g := (algebraMap S (Localization.AtPrime m)).comp
            (algebraMap P.Ring S)) hu).comp
          (algebraMap P.Ring (Localization N))
      exact (IsLocalization.lift_comp hu).symm
  let x : Fin d → E.ker := fun i ↦ P.localizedRelation m (f i)
  let _ : IsLocalRing E.Ring := by
    change IsLocalRing (Localization.AtPrime q)
    infer_instance
  let _ : Algebra P.toExtension.Ring E.Ring := by
    change Algebra P.Ring E.Ring
    infer_instance
  let _ : IsScalarTower K P.toExtension.Ring E.Ring := by
    change IsScalarTower K P.Ring E.Ring
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  let _ : Algebra.FormallyEtale P.toExtension.Ring E.Ring := by
    change Algebra.FormallyEtale P.Ring
      (Localization (m.primeCompl.comap (algebraMap P.Ring S)))
    infer_instance
  let _ : IsScalarTower P.toExtension.Ring E.Ring
      (Localization.AtPrime m) := by
    change IsScalarTower P.Ring E.Ring (Localization.AtPrime m)
    infer_instance
  let _ : IsScalarTower E.Ring (Localization.AtPrime m) m.ResidueField := by
    infer_instance
  let _ : IsScalarTower P.toExtension.Ring E.Ring m.ResidueField := by
    infer_instance
  let _ : Algebra (Localization.AtPrime q) (Localization.AtPrime m) := by
    change Algebra E.Ring (Localization.AtPrime m)
    infer_instance
  let _ : IsScalarTower K (Localization.AtPrime q)
      (Localization.AtPrime m) := by
    change IsScalarTower K E.Ring (Localization.AtPrime m)
    infer_instance
  let _ : IsScalarTower P.toExtension.Ring (Localization.AtPrime q)
      (Localization.AtPrime m) := by
    change IsScalarTower P.Ring E.Ring (Localization.AtPrime m)
    infer_instance
  let _ : IsScalarTower (Localization.AtPrime q) (Localization.AtPrime m)
      m.ResidueField := by
    infer_instance
  let _ : IsScalarTower P.toExtension.Ring (Localization.AtPrime q)
      m.ResidueField := by
    infer_instance
  let rhoRing : q.ResidueField →+* m.ResidueField :=
    Ideal.ResidueField.map q m (algebraMap P.toExtension.Ring S) rfl
  let rho : q.ResidueField →ₐ[P.toExtension.Ring] m.ResidueField :=
    { rhoRing with
      commutes' := fun a ↦ by
        change (Ideal.ResidueField.map q m
          (algebraMap P.toExtension.Ring S) rfl)
            (algebraMap P.toExtension.Ring q.ResidueField a) = _
        rw [Ideal.ResidueField.map_algebraMap]
        exact IsScalarTower.algebraMap_apply
          P.toExtension.Ring S m.ResidueField a }
  have hrho : Function.Bijective rho := by
    apply RingHom.SurjectiveOnStalks.residueFieldMap_bijective
    exact RingHom.surjectiveOnStalks_of_surjective
      P.toExtension.algebraMap_surjective
  let erho : q.ResidueField ≃ₐ[P.toExtension.Ring] m.ResidueField :=
    AlgEquiv.ofBijective rho hrho
  let residueChange : m.ResidueField ⊗[P.toExtension.Ring]
      Ω[P.toExtension.Ring⁄K] ≃ₗ[P.toExtension.Ring]
      q.ResidueField ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄K] :=
    TensorProduct.AlgebraTensorModule.congr erho.symm.toLinearEquiv
      (LinearEquiv.refl P.toExtension.Ring Ω[P.toExtension.Ring⁄K])
  let localE : IsLocalRing.CotangentSpace (Localization.AtPrime q) ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄K] :=
    (IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv
      ((erho.restrictScalars K).trans
        (m.residueFieldAlgEquivOfIsAlgClosed (K := K)))).trans <|
      ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
        K P.toExtension.Ring (Localization.AtPrime q)).symm.baseChange
          (Localization.AtPrime q) q.ResidueField _ _).trans <|
        TensorProduct.AlgebraTensorModule.cancelBaseChange P.toExtension.Ring
          (Localization.AtPrime q) q.ResidueField q.ResidueField
            Ω[P.toExtension.Ring⁄K]
  let cancelTarget :
      m.ResidueField ⊗[Localization.AtPrime m]
          ((Localization.AtPrime m) ⊗[E.Ring]
            Ω[E.Ring⁄K]) ≃ₗ[m.ResidueField]
        m.ResidueField ⊗[E.Ring] Ω[E.Ring⁄K] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange
      E.Ring (Localization.AtPrime m) m.ResidueField m.ResidueField Ω[E.Ring⁄K]
  let localizeDiff :
      m.ResidueField ⊗[E.Ring] Ω[E.Ring⁄K] ≃ₗ[m.ResidueField]
        m.ResidueField ⊗[E.Ring]
          (E.Ring ⊗[P.toExtension.Ring]
            Ω[P.toExtension.Ring⁄K]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      K P.toExtension.Ring E.Ring).symm.baseChange E.Ring m.ResidueField _ _
  let cancelSource :
      m.ResidueField ⊗[E.Ring]
          (E.Ring ⊗[P.toExtension.Ring]
            Ω[P.toExtension.Ring⁄K]) ≃ₗ[m.ResidueField]
        m.ResidueField ⊗[P.toExtension.Ring]
          Ω[P.toExtension.Ring⁄K] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange P.toExtension.Ring
      E.Ring m.ResidueField m.ResidueField Ω[P.toExtension.Ring⁄K]
  let complexE : m.ResidueField ⊗[Localization.AtPrime m] E.CotangentSpace ≃ₗ[K]
      q.ResidueField ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄K] :=
    (((cancelTarget.trans localizeDiff).trans cancelSource).restrictScalars K).trans
      (residueChange.restrictScalars K)
  have hlocalE (i : Fin d) :
      localE ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).toCotangent
        ⟨algebraMap P.toExtension.Ring (Localization.AtPrime q) (rel i),
          (IsLocalization.AtPrime.to_map_mem_maximal_iff
            (Localization.AtPrime q) q (rel i)).mpr (hrel' i)⟩) =
        (1 : q.ResidueField) ⊗ₜ[P.toExtension.Ring]
          KaehlerDifferential.D K P.toExtension.Ring (rel i) := by
    dsimp only [localE]
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      conormalEquiv_apply, LinearEquiv.baseChange_tmul,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    simp only [one_smul]
  have hliLocal : LinearIndependent q.ResidueField (fun i ↦
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)).toCotangent
        ⟨algebraMap P.toExtension.Ring (Localization.AtPrime q) (rel i),
          (IsLocalization.AtPrime.to_map_mem_maximal_iff
            (Localization.AtPrime q) q (rel i)).mpr (hrel' i)⟩) := by
    exact hli
  have hliTensor : LinearIndependent q.ResidueField (fun i ↦
      (1 : q.ResidueField) ⊗ₜ[P.toExtension.Ring]
        KaehlerDifferential.D K P.toExtension.Ring (rel i)) := by
    have hmap := hliLocal.map' localE.toLinearMap
      (LinearMap.ker_eq_bot.mpr localE.injective)
    change LinearIndependent q.ResidueField (fun i ↦ localE
      ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).toCotangent
        ⟨algebraMap P.toExtension.Ring (Localization.AtPrime q) (rel i),
          (IsLocalization.AtPrime.to_map_mem_maximal_iff
            (Localization.AtPrime q) q (rel i)).mpr (hrel' i)⟩)) at hmap
    simpa only [hlocalE] using hmap
  have hcomplexE (i : Fin d) :
      complexE ((E.cotangentComplex.baseChange m.ResidueField)
        (1 ⊗ₜ[Localization.AtPrime m]
          Algebra.Extension.Cotangent.mk (x i))) =
        (1 : q.ResidueField) ⊗ₜ[P.toExtension.Ring]
          KaehlerDifferential.D K P.toExtension.Ring (rel i) := by
    have hxi : (x i : E.Ring) =
        algebraMap P.toExtension.Ring E.Ring (rel i) := by
      dsimp only [x, localizedRelation, rel]
      change algebraMap P.Ring E.Ring (P.relation (f i)) =
        algebraMap P.Ring E.Ring (P.relation (f i))
      rfl
    change residueChange
      (((cancelTarget.trans localizeDiff).trans cancelSource)
        ((E.cotangentComplex.baseChange m.ResidueField)
          (1 ⊗ₜ[Localization.AtPrime m]
            Algebra.Extension.Cotangent.mk (x i)))) = _
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearMap.baseChange_tmul, Algebra.Extension.cotangentComplex_mk,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      LinearEquiv.baseChange_tmul, hxi,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul]
    simp [rel]
  have hliComplexK : LinearIndependent K (fun i ↦
      (E.cotangentComplex.baseChange m.ResidueField)
        (1 ⊗ₜ[Localization.AtPrime m]
          Algebra.Extension.Cotangent.mk (x i))) := by
    have hmapped : LinearIndependent K (fun i ↦ complexE
        ((E.cotangentComplex.baseChange m.ResidueField)
          (1 ⊗ₜ[Localization.AtPrime m]
            Algebra.Extension.Cotangent.mk (x i)))) := by
      simpa only [hcomplexE] using hliTensor.restrict_scalars' K
    exact hmapped.of_comp complexE.toLinearMap
  have hKsurj : Function.Surjective (algebraMap K m.ResidueField) := by
    intro y
    let e := m.residueFieldAlgEquivOfIsAlgClosed (K := K)
    refine ⟨e y, ?_⟩
    apply e.injective
    simp [e]
  have hliComplex : LinearIndependent m.ResidueField (fun i ↦
      (E.cotangentComplex.baseChange m.ResidueField)
        (1 ⊗ₜ[Localization.AtPrime m]
          Algebra.Extension.Cotangent.mk (x i))) := by
    have hmap := hliComplexK.map_of_surjective_injectiveₛ
      (algebraMap K m.ResidueField) (AddMonoidHom.id _)
      hKsurj Function.injective_id (fun k z ↦ by
        exact (IsScalarTower.algebraMap_smul m.ResidueField k z).symm)
    change LinearIndependent m.ResidueField (fun i ↦ AddMonoidHom.id _
      ((E.cotangentComplex.baseChange m.ResidueField)
        (1 ⊗ₜ[Localization.AtPrime m]
          Algebra.Extension.Cotangent.mk (x i)))) at hmap
    simpa only [AddMonoidHom.id_apply] using hmap
  exact hliComplex

/-- At a closed point of an algebraically closed finite-type algebra, select a
minimal family of presentation relations whose localized representatives have
linearly independent images under the residue-field base change of the
localized extension's cotangent-complex map. -/
theorem exists_relations_linearIndependent_localizedCotangentComplex
    {n r : ℕ} (P : Algebra.Presentation K S (Fin n) (Fin r))
    (m : Ideal S) [m.IsMaximal]
    (q : Ideal P.toExtension.Ring) [q.IsMaximal]
    (hq : q = m.comap (algebraMap P.toExtension.Ring S)) :
    let E : Algebra.Extension K (Localization.AtPrime m) :=
      P.toExtension.localization m.primeCompl
    ∃ f : Fin (Module.finrank m.ResidueField
        (LinearMap.ker (P.toExtension.toKaehler.baseChange m.ResidueField))) → Fin r,
      (∀ i, P.relation (f i) ∈ q) ∧
        LinearIndependent
          (IsLocalRing.ResidueField (Localization.AtPrime m)) (fun i ↦
            (E.cotangentComplex.baseChange
                (IsLocalRing.ResidueField (Localization.AtPrime m)))
              (1 ⊗ₜ[Localization.AtPrime m]
                Algebra.Extension.Cotangent.mk
                  (P.localizedRelation m (f i)))) := by
  obtain ⟨f, hrel, hli⟩ :=
    P.exists_relations_linearIndependent_localCotangent m q hq
  exact ⟨f, hrel,
    P.linearIndependent_localizedCotangentComplex_of_localCotangent
      m q hq f hrel hli⟩

end CotangentComplex

end Algebra.Presentation
