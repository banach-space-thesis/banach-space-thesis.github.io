import BanachIsometric.QuaternionicSeminormQuotient
import BanachIsometric.ProjectiveComparisonOverRing

/-! Canonical right-quaternionic bonding contractions between actual
seminorm quotients and their completions. All maps are Hopp linear; their
continuity and extension use the general non-field Mathlib APIs. -/

namespace BanachIsometric.Quaternionic

open UniformSpace

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]

private def seminormFactorOnModel {p q : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) : SeminormModel q →L[Hᵐᵒᵖ] SeminormQuotient p :=
  LinearMap.mkContinuous
    { toFun := fun x => seminormQuotientMap p x
      map_add' := fun x y => (seminormQuotientMap p).map_add x y
      map_smul' := fun a x => (seminormQuotientMap p).map_smul a x }
    1 (by intro x; simpa only [seminormQuotientMap_norm, norm_seminormModel, one_mul] using hpq x)

def seminormFactor {p q : RightSeminorm X} (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) :
    SeminormQuotient q →L[Hᵐᵒᵖ] SeminormQuotient p :=
  SeparationQuotient.liftCLM (seminormFactorOnModel hpq)
    (fun _ _ h => (h.map (seminormFactorOnModel hpq).continuous).eq)

@[simp] theorem seminormFactor_quotientMap {p q : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) (x : X) :
    seminormFactor hpq (seminormQuotientMap q x) = seminormQuotientMap p x := rfl

theorem seminormFactor_norm_le {p q : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) (x : SeminormQuotient q) :
    ‖seminormFactor hpq x‖ ≤ ‖x‖ := by
  obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective q x
  simpa only [seminormFactor_quotientMap, seminormQuotientMap_norm] using hpq x

theorem seminormFactor_surjective {p q : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) : Function.Surjective (seminormFactor hpq) := by
  intro y
  obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective p y
  exact ⟨seminormQuotientMap q x, rfl⟩

@[simp] theorem seminormFactor_refl (p : RightSeminorm X) :
    seminormFactor (le_refl p.toRealSeminorm) = ContinuousLinearMap.id Hᵐᵒᵖ (SeminormQuotient p) := by
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective p y
  rfl

theorem seminormFactor_comp {p q r : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) (hqr : q.toRealSeminorm ≤ r.toRealSeminorm) :
    (seminormFactor hpq).comp (seminormFactor hqr) = seminormFactor (hpq.trans hqr) := by
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective r y
  rfl

def completedSeminormFactor {p q : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) : SeminormCompletion q →L[Hᵐᵒᵖ] SeminormCompletion p :=
  ((Completion.toComplL : SeminormQuotient p →L[Hᵐᵒᵖ] SeminormCompletion p).comp
    (seminormFactor hpq)).extend
    (Completion.toComplL : SeminormQuotient q →L[Hᵐᵒᵖ] SeminormCompletion q)
    Completion.denseRange_coe (Completion.isUniformInducing_coe _)

@[simp] theorem completedSeminormFactor_coe {p q : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) (x : SeminormQuotient q) :
    completedSeminormFactor hpq (x : SeminormCompletion q) =
      ((seminormFactor hpq x : SeminormQuotient p) : SeminormCompletion p) :=
  ContinuousLinearMap.extend_eq _ _ _ _ x

@[simp] theorem completedSeminormFactor_completionMap {p q : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) (x : X) :
    completedSeminormFactor hpq (seminormCompletionMap q x) = seminormCompletionMap p x := by
  change completedSeminormFactor hpq ((seminormQuotientMap q x : SeminormQuotient q) : SeminormCompletion q) = _
  rw [completedSeminormFactor_coe, seminormFactor_quotientMap]
  rfl

theorem completedSeminormFactor_norm_le {p q : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) (x : SeminormCompletion q) :
    ‖completedSeminormFactor hpq x‖ ≤ ‖x‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_le (completedSeminormFactor hpq).continuous.norm continuous_norm
  · intro y
    simpa only [completedSeminormFactor_coe, Completion.norm_coe] using seminormFactor_norm_le hpq y

theorem completedSeminormFactor_denseRange {p q : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) : DenseRange (completedSeminormFactor hpq) := by
  apply (Completion.denseRange_coe : DenseRange ((↑) : SeminormQuotient p → SeminormCompletion p)).mono
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := seminormFactor_surjective hpq y
  refine ⟨(x : SeminormCompletion q), ?_⟩
  rw [completedSeminormFactor_coe, hx]

@[simp] theorem completedSeminormFactor_refl (p : RightSeminorm X) :
    completedSeminormFactor (le_refl p.toRealSeminorm) = ContinuousLinearMap.id Hᵐᵒᵖ (SeminormCompletion p) := by
  apply ContinuousLinearMap.coeFn_injective
  apply Completion.ext (completedSeminormFactor (le_refl p.toRealSeminorm)).continuous continuous_id
  intro y
  simp only [completedSeminormFactor_coe, seminormFactor_refl, ContinuousLinearMap.id_apply]
  rfl

theorem completedSeminormFactor_comp {p q r : RightSeminorm X}
    (hpq : p.toRealSeminorm ≤ q.toRealSeminorm) (hqr : q.toRealSeminorm ≤ r.toRealSeminorm) :
    (completedSeminormFactor hpq).comp (completedSeminormFactor hqr) = completedSeminormFactor (hpq.trans hqr) := by
  apply ContinuousLinearMap.coeFn_injective
  apply Completion.ext
    ((completedSeminormFactor hpq).continuous.comp (completedSeminormFactor hqr).continuous)
    (completedSeminormFactor (hpq.trans hqr)).continuous
  intro y
  change completedSeminormFactor hpq (completedSeminormFactor hqr y) = _
  simp only [completedSeminormFactor_coe]
  exact congrArg ((↑) : SeminormQuotient p → SeminormCompletion p) (DFunLike.congr_fun (seminormFactor_comp hpq hqr) y)

theorem seminormCompletionMap_isUniformInducing_model (p : RightSeminorm X) :
    IsUniformInducing (fun x : SeminormModel p => seminormCompletionMap p x) := by
  change IsUniformInducing (fun x : SeminormModel p => ((SeparationQuotient.mk x : SeminormQuotient p) : SeminormCompletion p))
  exact (Completion.isUniformInducing_coe _).comp SeparationQuotient.isUniformInducing_mk

end
end BanachIsometric.Quaternionic
