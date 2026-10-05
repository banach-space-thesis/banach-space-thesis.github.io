import Posets.WolfePreservationNecessaryLift

/-! Quantitative atomic inputs to the necessity direction of the Wolfe
criterion. A norming pairing forces mass on large coordinates, while each
atomic row has a uniformly bounded finite overlap. These estimates do not
assert the subsequent topological disjointization. -/

noncomputable section
open Set Filter Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜]

theorem wolfe_pairing_large_coordinates (a : JLMS.ellOneOn 𝕜 K)
    (b : K → 𝕜) {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hb : ∀ y, ‖b y‖ ≤ B) {c : 𝕜} (hpair : HasSum (fun y => a y * b y) c) :
    ‖c‖ ≤ B * ‖JLMS.restrictionL1 {y | δ ≤ ‖b y‖} a‖ + δ * ‖a‖ := by
  classical
  let U : Set K := {y | δ ≤ ‖b y‖}
  have ha : HasSum (fun y => ‖a y‖) ‖a‖ := by
    simpa only [JLMS.ellOneOn_norm_eq_tsum] using (JLMS.ellOneOn_summable_norm a).hasSum
  have hu : HasSum (fun y => ‖JLMS.restrictionL1 U a y‖)
      ‖JLMS.restrictionL1 U a‖ := by
    simpa only [JLMS.ellOneOn_norm_eq_tsum] using
      (JLMS.ellOneOn_summable_norm (JLMS.restrictionL1 U a)).hasSum
  apply hpair.norm_le_of_bounded ((hu.mul_left B).add (ha.mul_left δ))
  intro y
  rw [norm_mul]
  by_cases hy : y ∈ U
  · simp only [JLMS.restrictionL1_apply, JLMS.restrictL1_apply, hy, if_true]
    nlinarith [norm_nonneg (a y), hb y]
  · have hyd : ‖b y‖ < δ := lt_of_not_ge hy
    simp only [JLMS.restrictionL1_apply, JLMS.restrictL1_apply, hy, if_false,
      norm_zero, mul_zero, zero_add]
    nlinarith [norm_nonneg (a y)]

theorem wolfe_large_coordinates_mass_lower (a : JLMS.ellOneOn 𝕜 K)
    (b : K → 𝕜) {A B d : ℝ} (hB : 0 < B) (hd : 0 < d)
    (ha : ‖a‖ ≤ A) (hb : ∀ y, ‖b y‖ ≤ B)
    {c : 𝕜} (hpair : HasSum (fun y => a y * b y) c)
    (hc : d ≤ ‖c‖) :
    d / (2 * B) ≤ ‖JLMS.restrictionL1 {y | d / (2 * (A + 1)) ≤ ‖b y‖} a‖ := by
  have hA : 0 ≤ A := (norm_nonneg a).trans ha
  have hp : 0 < 2 * (A + 1) := by positivity
  have h := wolfe_pairing_large_coordinates a b hB.le
    (show 0 ≤ d / (2 * (A + 1)) by positivity) hb hpair
  have hsmall : d / (2 * (A + 1)) * ‖a‖ ≤ d / 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 2 * B)).mpr
  nlinarith

theorem wolfe_large_coordinates_finset_bound (a : JLMS.ellOneOn 𝕜 L)
    {δ : ℝ} (s : Finset L) (hs : ∀ x ∈ s, δ ≤ ‖a x‖) :
    (s.card : ℝ) * δ ≤ ‖a‖ := by
  calc
    (s.card : ℝ) * δ = ∑ x ∈ s, δ := by simp
    _ ≤ ∑ x ∈ s, ‖a x‖ := Finset.sum_le_sum hs
    _ ≤ ∑' x, ‖a x‖ := (JLMS.ellOneOn_summable_norm a).sum_le_tsum s
      (fun _ _ => norm_nonneg _)
    _ = ‖a‖ := (JLMS.ellOneOn_norm_eq_tsum a).symm

end Posets
