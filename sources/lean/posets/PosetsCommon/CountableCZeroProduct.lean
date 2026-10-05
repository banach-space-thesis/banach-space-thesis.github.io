import JFA.CountableCZeroRetracts
import Mathlib.Logic.Denumerable

noncomputable section
open scoped ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
variable {ι κ : Type} [TopologicalSpace ι] [DiscreteTopology ι]
  [TopologicalSpace κ] [DiscreteTopology κ]

/-- Numbering the disjoint union identifies the two coordinate spaces with scalar c₀. -/
def cZeroProductNumberingEquiv (e : (ι ⊕ κ) ≃ ℕ) :
    (C₀(ι, 𝕜) × C₀(κ, 𝕜)) ≃L[𝕜] JFA.cZero 𝕜 := by
  let eI : ι ↪ ℕ := ⟨fun i => e (Sum.inl i), e.injective.comp Sum.inl_injective⟩
  let eK : κ ↪ ℕ := ⟨fun k => e (Sum.inr k), e.injective.comp Sum.inr_injective⟩
  have hne (i : ι) (k : κ) : eI i ≠ eK k := fun h => Sum.noConfusion (e.injective h)
  let AI := cZeroExtend (𝕜 := 𝕜) (X := 𝕜) eI
  let AK := cZeroExtend (𝕜 := 𝕜) (X := 𝕜) eK
  let BI := cZeroRestrict (𝕜 := 𝕜) (X := 𝕜) eI
  let BK := cZeroRestrict (𝕜 := 𝕜) (X := 𝕜) eK
  have hII (a : C₀(ι, 𝕜)) : BI (AI a) = a :=
    congrArg (fun T => T a) (cZeroRestrict_comp_extend (𝕜 := 𝕜) (X := 𝕜) eI)
  have hKK (b : C₀(κ, 𝕜)) : BK (AK b) = b :=
    congrArg (fun T => T b) (cZeroRestrict_comp_extend (𝕜 := 𝕜) (X := 𝕜) eK)
  have hIK (b : C₀(κ, 𝕜)) : BI (AK b) = 0 :=
    congrArg (fun T => T b) (JFA.cZeroRestrict_extend_zero (𝕜 := 𝕜) eI eK hne)
  have hKI (a : C₀(ι, 𝕜)) : BK (AI a) = 0 :=
    congrArg (fun T => T a) (JFA.cZeroRestrict_extend_zero (𝕜 := 𝕜) eK eI
      (fun k i => (hne i k).symm))
  refine ContinuousLinearEquiv.equivOfInverse (AI.coprod AK) (BI.prod BK) ?_ ?_
  · intro x
    apply Prod.ext
    · change BI (AI x.1 + AK x.2) = x.1
      rw [map_add, hII, hIK, add_zero]
    · change BK (AI x.1 + AK x.2) = x.2
      rw [map_add, hKI, hKK, zero_add]
  · intro f
    ext n
    obtain ⟨p, rfl⟩ := e.surjective n
    cases p with
    | inl i =>
      change AI (BI f) (eI i) + AK (BK f) (eI i) = f (eI i)
      have hzero : AK (BK f) (eI i) = 0 := congrArg (fun g => g i) (hIK (BK f))
      rw [hzero, add_zero]
      exact cZeroExtend_apply_image eI (BI f) i
    | inr k =>
      change AI (BI f) (eK k) + AK (BK f) (eK k) = f (eK k)
      have hzero : AI (BI f) (eK k) = 0 := congrArg (fun g => g k) (hKI (BI f))
      rw [hzero, zero_add]
      exact cZeroExtend_apply_image eK (BK f) k

def countableCZeroProductEquiv [Countable ι] [Countable κ] [Infinite ι] :
    (C₀(ι, 𝕜) × C₀(κ, 𝕜)) ≃L[𝕜] JFA.cZero 𝕜 :=
  cZeroProductNumberingEquiv (Classical.choice (inferInstance : Nonempty ((ι ⊕ κ) ≃ ℕ)))

end ThesisCommon
