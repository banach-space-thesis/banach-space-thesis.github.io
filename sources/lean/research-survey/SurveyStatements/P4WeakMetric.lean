import SurveyStatements.P4WeakCompact
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Sequences

/-!
# Metrizability of weakly compact subsets of separable spaces

This proves `p5:lem:weak-compact-metrizable`. A countable family of
Hahn-Banach functionals separates points. Their evaluations embed each
weakly compact subset into a countable product of scalar fields.
-/

noncomputable section
set_option autoImplicit false

open Set Filter Topology TopologicalSpace

namespace SurveyStatements.P4

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A separable normed space has countably many continuous functionals which
jointly separate every vector from zero. -/
theorem exists_countable_total_dual [SeparableSpace E] :
    ∃ D : Set (E →L[𝕜] 𝕜), D.Countable ∧
      ∀ x : E, (∀ φ ∈ D, φ x = 0) → x = 0 := by
  classical
  obtain ⟨D, hD, hdense⟩ := exists_countable_dense E
  choose φ hφ hφx using fun x : E => exists_dual_vector'' 𝕜 x
  refine ⟨φ '' D, hD.image φ, ?_⟩
  intro x hx
  by_contra hne
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
  obtain ⟨y, hyD, hnear⟩ := hdense.exists_dist_lt x (by positivity : 0 < ‖x‖ / 4)
  have hzero : φ y x = 0 := hx _ ⟨y, hyD, rfl⟩
  have hy : ‖y‖ ≤ ‖y - x‖ := by
    calc
      ‖y‖ = ‖φ y (y - x)‖ := by
        rw [map_sub, hzero, sub_zero, hφx, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖φ y‖ * ‖y - x‖ := (φ y).le_opNorm _
      _ ≤ ‖y - x‖ := by
        simpa using mul_le_mul_of_nonneg_right (hφ y) (norm_nonneg (y - x))
  have ht := norm_add_le (x - y) y
  rw [sub_add_cancel] at ht
  rw [dist_eq_norm] at hnear
  rw [norm_sub_rev y x] at hy
  nlinarith

/-- A weakly compact subset of a separable normed space is metrizable in its
weak topology. The subtype topology here is the actual weak topology. -/
theorem weakCompact_metrizable [SeparableSpace E]
    {K : Set (WeakSpace 𝕜 E)} (hK : IsCompact K) : MetrizableSpace K := by
  classical
  obtain ⟨D, hD, htotal⟩ := exists_countable_total_dual (𝕜 := 𝕜) (E := E)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : Countable D := hD.to_subtype
  let c : K → (D → 𝕜) := fun x φ => φ.val ((toWeakSpace 𝕜 E).symm x.val)
  have hc : Continuous c := by
    apply continuous_pi
    intro φ
    exact (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip φ.val).comp
      continuous_subtype_val
  have hinj : Function.Injective c := by
    intro x y hxy
    apply Subtype.ext
    apply (toWeakSpace 𝕜 E).symm.injective
    apply sub_eq_zero.mp
    apply htotal
    intro φ hφ
    have he := congrFun hxy ⟨φ, hφ⟩
    simpa only [c, map_sub, sub_eq_zero] using he
  exact (hc.isClosedEmbedding hinj).isEmbedding.metrizableSpace

/-- Every sequence in a weakly compact set of a separable normed space has a
weakly convergent subsequence whose limit belongs to that set. -/
theorem exists_weakly_convergent_subsequence [SeparableSpace E]
    {K : Set (WeakSpace 𝕜 E)} (hK : IsCompact K) (s : ℕ → K) :
    ∃ x : K, ∃ r : ℕ → ℕ, StrictMono r ∧
      Tendsto (fun n => (s (r n)).val) atTop (𝓝 x.val) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : MetrizableSpace K := weakCompact_metrizable hK
  obtain ⟨x, r, hr, hx⟩ := CompactSpace.tendsto_subseq s
  exact ⟨x, r, hr, (continuous_subtype_val.tendsto x).comp hx⟩

end SurveyStatements.P4
