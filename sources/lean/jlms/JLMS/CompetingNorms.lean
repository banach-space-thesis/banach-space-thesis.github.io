import JLMS.Definitions
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Applying open mapping to an arbitrary competing norm

The competing norm receives its own normed-space topology, on a type synonym
of the original vector space. Its epsilon–N completeness hypothesis gives
completeness for that topology. A lower comparison with a Banach-space norm
makes the identity continuous in one direction, and open mapping supplies
the reverse comparison.
-/

noncomputable section

open Filter Topology

namespace JLMS

section Construction

variable (𝕜 : Type*) [RCLike 𝕜]
variable {A : Type*} [AddCommGroup A] [Module 𝕜 A]

/-- The original vector space equipped with its explicitly supplied norm. -/
def WithVectorNorm (n : A → ℝ) (_hn : IsVectorNorm 𝕜 n) := A

instance withVectorNormAddGroup (n : A → ℝ) (hn : IsVectorNorm 𝕜 n) :
    AddCommGroup (WithVectorNorm 𝕜 n hn) := inferInstanceAs (AddCommGroup A)

instance withVectorNormModule (n : A → ℝ) (hn : IsVectorNorm 𝕜 n) :
    Module 𝕜 (WithVectorNorm 𝕜 n hn) := inferInstanceAs (Module 𝕜 A)

instance withVectorNormNorm (n : A → ℝ) (hn : IsVectorNorm 𝕜 n) :
    Norm (WithVectorNorm 𝕜 n hn) := ⟨n⟩

def withVectorNormCore (n : A → ℝ) (hn : IsVectorNorm 𝕜 n) :
    NormedSpace.Core 𝕜 (WithVectorNorm 𝕜 n hn) where
  norm_nonneg := hn.1
  norm_smul := hn.2.2.2
  norm_triangle := hn.2.2.1
  norm_eq_zero_iff := hn.2.1

instance withVectorNormGroup (n : A → ℝ) (hn : IsVectorNorm 𝕜 n) :
    NormedAddCommGroup (WithVectorNorm 𝕜 n hn) := NormedAddCommGroup.ofCore (withVectorNormCore 𝕜 n hn)

instance withVectorNormSpace (n : A → ℝ) (hn : IsVectorNorm 𝕜 n) :
    NormedSpace 𝕜 (WithVectorNorm 𝕜 n hn) := NormedSpace.ofCore (withVectorNormCore 𝕜 n hn)

theorem completeSpace_withVectorNorm (n : A → ℝ) (hn : IsVectorNorm 𝕜 n)
    (hc : CompleteNorm n) : CompleteSpace (WithVectorNorm 𝕜 n hn) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have huc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ i j : ℕ, N ≤ i → N ≤ j → n (u i - u j) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun i j hi hj => ?_⟩
    change ‖u i - u j‖ < ε
    simpa only [dist_eq_norm] using hN i hi j hj
  obtain ⟨y, hy⟩ := hc u huc
  refine ⟨y, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  simpa only [dist_eq_norm] using hy ε hε

end Construction

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A] [CompleteSpace A]

/-- A complete vector norm dominating a Banach norm also admits an upper
comparison, by the Banach open mapping theorem for the identity map. -/
theorem completeNorm_upper_bound_of_lower (n : A → ℝ) (hn : IsVectorNorm 𝕜 n)
    (hc : CompleteNorm n) {c : ℝ} (hpos : 0 < c) (hlower : ∀ x, c * ‖x‖ ≤ n x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, n x ≤ C * ‖x‖ := by
  let V := WithVectorNorm 𝕜 n hn
  letI : CompleteSpace V := completeSpace_withVectorNorm 𝕜 n hn hc
  let e : V ≃ₗ[𝕜] A := LinearEquiv.refl 𝕜 A
  have hbound (x : V) : ‖e x‖ ≤ c⁻¹ * ‖x‖ := by
    change ‖e x‖ ≤ c⁻¹ * n x
    have h := hlower x
    have hdiv := (le_div_iff₀ hpos).mpr (by simpa [mul_comm] using h)
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  let L := e.toLinearMap.mkContinuous c⁻¹ hbound
  let E := e.toContinuousLinearEquivOfContinuous L.continuous
  let C := ‖E.symm.toContinuousLinearMap‖ + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro x
  have h := E.symm.toContinuousLinearMap.le_opNorm x
  change n x ≤ ‖E.symm.toContinuousLinearMap‖ * ‖x‖ at h
  exact h.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg x))

end JLMS
