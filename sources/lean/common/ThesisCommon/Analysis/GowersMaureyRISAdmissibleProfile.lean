import ThesisCommon.Analysis.GowersMaureyFormsEnvelope
import ThesisCommon.Analysis.GowersMaureyRISNormEstimate

/-! The RIS estimate in the actual constructed shift space, for an
admissible numerical profile. All local norming hypotheses are discharged
from the concrete implicit norm. Existence of the interpolating profiles
of source Lemma 6 is a separate numerical assertion. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem RISData.sum_coordinate_le_one {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (n : ℕ) :
    ‖(∑ i, x i) n‖ ≤ 1 :=
  successive_partial_sum_coordinate_bound h.successive
    (fun i j => (coordinate_le_implicitNorm D (x i) j).trans (h.vector_norm_le_one i))
    Finset.univ n

theorem RISData.exists_norming_form {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (g : ℕ → ℝ)
    (hgpos : ∀ k, 2 ≤ k → 0 < g k)
    (hgf : ∀ k, 2 ≤ k → g k ≤ logarithmicWeight k)
    (hgspecial : ∀ k, k ∈ D.specialSizes → g k ≤ Real.sqrt (logarithmicWeight k))
    (E : Interval) {r : ℝ} (hr : 1 ≤ r)
    (hn : r < implicitNorm D (GowersMaurey.restrict E (∑ i, x i))) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ a : C00 𝕜, IsForm D k (g k) a ∧
      r < ‖pairing a (GowersMaurey.restrict E (∑ i, x i))‖ := by
  apply exists_norming_form_of_coordinate_bound D g hgpos hgf hgspecial _ _ hn
  intro n
  rw [restrict_apply]
  split_ifs
  · exact (h.sum_coordinate_le_one n).trans hr
  · simpa only [norm_zero] using zero_le_one.trans hr

theorem RISData.sum_norm_le_of_admissible_profile
    {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (G : ℝ → ℝ) (g : ℕ → ℝ) {d : ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 0) G) (hmono : MonotoneOn G (Set.Ici 0))
    (hsmallG : ∀ t, 0 ≤ t → t ≤ 1 → G t = t) (hd : 0 ≤ d)
    (hderiv : HasDerivWithinAt G d (Set.Ioi 1) 1)
    (hgap : 1 / (4 * Real.log 2) ≤ 1 - d)
    (hmul : ∀ r s, 0 ≤ r → 0 ≤ s → G r * G s ≤ G (r * s))
    (hg : ∀ k : ℕ, 2 ≤ k → Real.sqrt (logarithmicWeight k) ≤ g k)
    (hgf : ∀ k : ℕ, 2 ≤ k → g k ≤ logarithmicWeight k)
    (hgspecial : ∀ k, k ∈ D.specialSizes → g k ≤ Real.sqrt (logarithmicWeight k))
    (hgprofile : ∀ k : ℕ, 1 ≤ k → (g k)⁻¹ * k = G k) :
    implicitNorm D (∑ i, x i) ≤ (1 + 2 * ε) * G N := by
  have hgpos : ∀ k, 2 ≤ k → 0 < g k := by
    intro k hk
    exact (Real.sqrt_pos.mpr (zero_lt_one.trans_le
      (one_le_logarithmicWeight (by omega)))).trans_le (hg k hk)
  exact h.sum_norm_le_of_profile G g hG hmono hsmallG hd hderiv hgap hmul hg hgprofile
    (fun E r hr hn => h.exists_norming_form g hgpos hgf hgspecial E hr hn)

end ThesisCommon.GowersMaurey
