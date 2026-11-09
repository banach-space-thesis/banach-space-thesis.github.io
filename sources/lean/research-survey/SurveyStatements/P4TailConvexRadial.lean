import SurveyStatements.P4TailConvexParameter
import Mathlib.Tactic.Linarith

/-! Radial truncation removes the auxiliary uniform bound on the continuous
approximants in the parameter tail-convexification theorem. -/

noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped BigOperators

namespace SurveyStatements.P4

variable {K E : Type*} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Norm Baire class one: an actual pointwise norm limit of continuous maps. -/
def IsNormBaireOne (f : K → E) : Prop :=
  ∃ u : ℕ → C(K, E), ∀ t, Tendsto (fun n => u n t) atTop (𝓝 (f t))

def boundedRadial (B : ℝ) (x : E) : E := (B / max B ‖x‖) • x

lemma boundedRadial_continuous (B : ℝ) (hB : 0 < B) :
    Continuous (boundedRadial (E := E) B) :=
  (continuous_const.div (continuous_const.max continuous_norm)
    (fun x => ne_of_gt (hB.trans_le (le_max_left B ‖x‖)))).smul continuous_id

lemma boundedRadial_norm_le (B : ℝ) (hB : 0 < B) (x : E) :
    ‖boundedRadial B x‖ ≤ B := by
  have hm : 0 < max B ‖x‖ := hB.trans_le (le_max_left B ‖x‖)
  rw [boundedRadial, norm_smul, Real.norm_of_nonneg (div_nonneg hB.le hm.le)]
  calc
    B / max B ‖x‖ * ‖x‖ ≤ B / max B ‖x‖ * max B ‖x‖ :=
      mul_le_mul_of_nonneg_left (le_max_right B ‖x‖) (div_nonneg hB.le hm.le)
    _ = B := div_mul_cancel₀ B (ne_of_gt hm)

lemma boundedRadial_eq (B : ℝ) (hB : 0 < B) {x : E} (hx : ‖x‖ ≤ B) :
    boundedRadial B x = x := by
  simp only [boundedRadial, max_eq_left hx, div_self (ne_of_gt hB), one_smul]

lemma weak_pointwise_limit_norm_le [CompactSpace K]
    (fseq : ℕ → C(K, E)) (C : ℝ) (hbound : ∀ n, ‖fseq n‖ ≤ C)
    (f : K → E)
    (hweak : ∀ t (φ : StrongDual ℝ E),
      Tendsto (fun n => φ (fseq n t)) atTop (𝓝 (φ (f t)))) :
    ∀ t, ‖f t‖ ≤ C := by
  intro t
  obtain ⟨φ, hφ, hφx⟩ := exists_dual_vector'' ℝ (f t)
  have hlim : Tendsto (fun n => φ (fseq n t)) atTop (𝓝 ‖f t‖) := by
    simpa [hφx] using hweak t φ
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  calc
    φ (fseq n t) ≤ ‖φ (fseq n t)‖ := Real.le_norm_self _
    _ ≤ ‖φ‖ * ‖fseq n t‖ := φ.le_opNorm _
    _ ≤ 1 * ‖fseq n t‖ := mul_le_mul_of_nonneg_right hφ (norm_nonneg _)
    _ ≤ C := by simpa using ((fseq n).norm_coe_le_norm t).trans (hbound n)

/-- The full parameter tail-convexification statement: its hypotheses are
uniform boundedness, weak pointwise convergence, and genuine norm Baire class
one of the limit. The parameter set and full dual need not be separable. -/
theorem parameter_tail_convexification [CompactSpace K] [T2Space K]
    (fseq : ℕ → C(K, E)) (C : ℝ) (hbound : ∀ n, ‖fseq n‖ ≤ C)
    (f : K → E)
    (hweak : ∀ t (φ : StrongDual ℝ E),
      Tendsto (fun n => φ (fseq n t)) atTop (𝓝 (φ (f t))))
    (hBaire : IsNormBaireOne f) :
    ∃ (F : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ),
      (∀ k n, 0 ≤ a k n) ∧ (∀ k, ∑ n ∈ F k, a k n = 1) ∧
      (∀ k n, n ∈ F k → k ≤ n) ∧
      ∀ t, Tendsto (fun k => ∑ n ∈ F k, a k n • fseq n t) atTop (𝓝 (f t)) := by
  obtain ⟨u, hu⟩ := hBaire
  have hC : 0 ≤ C := (norm_nonneg (fseq 0)).trans (hbound 0)
  let B := C + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let v : ℕ → C(K, E) := fun n =>
    ⟨fun t => boundedRadial B (u n t),
      (boundedRadial_continuous B hB).comp (u n).continuous⟩
  have hvbound : ∀ n, ‖v n‖ ≤ B := by
    intro n
    apply (ContinuousMap.norm_le _ hB.le).mpr
    intro t
    exact boundedRadial_norm_le B hB _
  have hv : ∀ t, Tendsto (fun n => v n t) atTop (𝓝 (f t)) := by
    intro t
    have ht := ((boundedRadial_continuous B hB).tendsto (f t)).comp (hu t)
    have heq : boundedRadial B (f t) = f t :=
      boundedRadial_eq B hB ((weak_pointwise_limit_norm_le fseq C hbound f hweak t).trans
        (by dsimp [B]; linarith))
    simpa only [v, heq] using ht
  exact parameter_tail_convexification_bounded fseq C hbound f hweak v B hvbound hv

end SurveyStatements.P4
