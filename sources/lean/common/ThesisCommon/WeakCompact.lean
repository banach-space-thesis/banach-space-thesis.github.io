import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-! Weak compactness uses the actual weak topology, not weak-star topology.
The compact-cover formulation is equivalent to compactness of the weak closure
in the Hausdorff weak topology of a normed space. No sequential criterion is used. -/
noncomputable section
open Set Topology
open scoped Pointwise
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The image of the closed unit ball has a weakly compact containing set. -/
def IsWeaklyCompactOperator (T : E →L[𝕜] F) : Prop :=
  ∃ K : Set (WeakSpace 𝕜 F), IsCompact K ∧
    ∀ x : E, ‖x‖ ≤ 1 → toWeakSpace 𝕜 F (T x) ∈ K

theorem weaklyCompact_zero : IsWeaklyCompactOperator (0 : E →L[𝕜] F) := by
  exact ⟨{0}, isCompact_singleton, by intro x hx; simp⟩

theorem IsWeaklyCompactOperator.add {S T : E →L[𝕜] F}
    (hS : IsWeaklyCompactOperator S) (hT : IsWeaklyCompactOperator T) :
    IsWeaklyCompactOperator (S + T) := by
  obtain ⟨K, hK, hSK⟩ := hS
  obtain ⟨L, hL, hTL⟩ := hT
  refine ⟨K + L, hK.add hL, ?_⟩
  intro x hx
  exact Set.add_mem_add (hSK x hx) (hTL x hx)

theorem IsWeaklyCompactOperator.smul {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator T) (a : 𝕜) : IsWeaklyCompactOperator (a • T) := by
  obtain ⟨K, hK, hTK⟩ := hT
  refine ⟨(fun y : WeakSpace 𝕜 F => a • y) '' K,
    hK.image (continuous_const.smul continuous_id), ?_⟩
  intro x hx
  exact ⟨toWeakSpace 𝕜 F (T x), hTK x hx, rfl⟩

theorem IsWeaklyCompactOperator.comp_left {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator T) (S : F →L[𝕜] G) :
    IsWeaklyCompactOperator (S.comp T) := by
  obtain ⟨K, hK, hTK⟩ := hT
  refine ⟨WeakSpace.map S '' K, hK.image (WeakSpace.map S).continuous, ?_⟩
  intro x hx
  exact ⟨toWeakSpace 𝕜 F (T x), hTK x hx, rfl⟩

theorem IsWeaklyCompactOperator.comp_right {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator T) (S : G →L[𝕜] E) :
    IsWeaklyCompactOperator (T.comp S) := by
  obtain ⟨K, hK, hTK⟩ := hT
  let r : ℝ := ‖S‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let a : 𝕜 := r
  have ha : a ≠ 0 := by simpa [a] using ne_of_gt hr
  have hna : ‖a‖ = r := by simp [a, abs_of_pos hr]
  refine ⟨(fun y : WeakSpace 𝕜 F => a • y) '' K,
    hK.image (continuous_const.smul continuous_id), ?_⟩
  intro x hx
  have hSx : ‖S x‖ ≤ r := (S.le_opNorm x).trans <|
    (mul_le_of_le_one_right (norm_nonneg S) hx).trans (by dsimp [r]; linarith)
  have hunit : ‖a⁻¹ • S x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hna, ← div_eq_inv_mul]
    exact (div_le_one hr).mpr hSx
  refine ⟨toWeakSpace 𝕜 F (T (a⁻¹ • S x)), hTK _ hunit, ?_⟩
  change toWeakSpace 𝕜 F (a • T (a⁻¹ • S x)) = _
  simp [map_smul, smul_smul, ha]

/-- The actual linear subspace of weakly compact operators. -/
def weaklyCompactSubmodule (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {T | IsWeaklyCompactOperator T}
  zero_mem' := weaklyCompact_zero
  add_mem' := IsWeaklyCompactOperator.add
  smul_mem' := fun a _ h => h.smul a

/-- Distance in operator norm to W(E,F). -/
def weakEssentialNorm (T : E →L[𝕜] F) : ℝ :=
  sInf {r : ℝ | ∃ W : E →L[𝕜] F, IsWeaklyCompactOperator W ∧ r = ‖T - W‖}

theorem weakEssentialNorm_nonneg (T : E →L[𝕜] F) : 0 ≤ weakEssentialNorm T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨W, hW, rfl⟩
    exact norm_nonneg _

theorem weakEssentialNorm_le (T : E →L[𝕜] F) {W : E →L[𝕜] F}
    (hW : IsWeaklyCompactOperator W) : weakEssentialNorm T ≤ ‖T - W‖ := by
  apply csInf_le
  · exact ⟨0, by rintro r ⟨V, hV, rfl⟩; exact norm_nonneg _⟩
  · exact ⟨W, hW, rfl⟩

theorem weakEssentialNorm_le_norm (T : E →L[𝕜] F) : weakEssentialNorm T ≤ ‖T‖ := by
  simpa using weakEssentialNorm_le T weaklyCompact_zero

theorem IsWeaklyCompactOperator.weakEssentialNorm_eq_zero {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator T) : weakEssentialNorm T = 0 := by
  exact le_antisymm (by simpa using weakEssentialNorm_le T hT) (weakEssentialNorm_nonneg T)

end ThesisCommon
