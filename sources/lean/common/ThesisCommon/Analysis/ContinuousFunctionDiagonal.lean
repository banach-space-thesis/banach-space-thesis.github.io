import ThesisCommon.Analysis.ContinuousFunctionTensorMaps
import Mathlib.Topology.CompactOpen

/-! The actual diagonal-evaluation operator on twice continuous scalar functions.
It has norm one and cannot act by a fixed coefficient functional on a clopen
set containing two points separated by a clopen set. This is an obstruction to
local coefficient compression, not a statement about primary factorisation. -/
noncomputable section
open Set Topology
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K] [CompactSpace K] [T2Space K]

def continuousFunctionDiagonal : C(K, C(K, 𝕜)) →L[𝕜] C(K, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.uncurry.comp
        ⟨fun t => (t, t), continuous_id.prodMk continuous_id⟩
      map_add' := fun f g => by ext t; rfl
      map_smul' := fun c f => by ext t; rfl }
    1 (fun f => by
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro t
      exact ((f t).norm_coe_le_norm t).trans (f.norm_coe_le_norm t))

@[simp] theorem continuousFunctionDiagonal_apply (f : C(K, C(K, 𝕜))) (t : K) :
    continuousFunctionDiagonal (𝕜 := 𝕜) f t = f t t := rfl

theorem norm_continuousFunctionDiagonal_le :
    ‖continuousFunctionDiagonal (𝕜 := 𝕜) (K := K)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem norm_continuousFunctionDiagonal [Nonempty K] :
    ‖continuousFunctionDiagonal (𝕜 := 𝕜) (K := K)‖ = 1 := by
  apply le_antisymm norm_continuousFunctionDiagonal_le
  let f : C(K, C(K, 𝕜)) := ContinuousMap.const _ (ContinuousMap.const _ 1)
  obtain ⟨t⟩ := ‹Nonempty K›
  have h := ((continuousFunctionDiagonal (𝕜 := 𝕜) f).norm_coe_le_norm t).trans
    ((continuousFunctionDiagonal (𝕜 := 𝕜)).le_opNorm f)
  simpa [f] using h

/-- A fixed coefficient functional cannot represent diagonal evaluation on a
clopen set whose two points are distinguished by another clopen set. -/
theorem continuousFunctionDiagonal_not_local_coefficient
    (A D : Set K) (hA : IsClopen A) (hD : IsClopen D)
    {s t : K} (hs : s ∈ A) (ht : t ∈ A) (hsD : s ∈ D) (htD : t ∉ D) :
    ¬ ∃ u : C(K, 𝕜) →L[𝕜] 𝕜,
      ∀ f : C(K, C(K, 𝕜)), (∀ v, v ∉ A → f v = 0) →
        ∀ v ∈ A, continuousFunctionDiagonal (𝕜 := 𝕜) f v = u (f v) := by
  rintro ⟨u, hu⟩
  let χ : C(K, 𝕜) := continuousFunctionMask (𝕜 := 𝕜) D hD
    (ContinuousMap.const _ 1)
  let f : C(K, C(K, 𝕜)) := continuousFunctionMask (𝕜 := 𝕜) A hA
    (ContinuousMap.const _ χ)
  have hf : ∀ v, v ∉ A → f v = 0 := by
    intro v hv
    simp [f, hv]
  have hs' : (1 : 𝕜) = u χ := by
    simpa [f, χ, hs, hsD] using hu f hf s hs
  have ht' : (0 : 𝕜) = u χ := by
    simpa [f, χ, ht, htD] using hu f hf t ht
  exact one_ne_zero (hs'.trans ht'.symm)

end ThesisCommon
