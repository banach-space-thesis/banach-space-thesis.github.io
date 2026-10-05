import ThesisCommon.Analysis.GowersMaureyRISNormEstimate
import ThesisCommon.Analysis.GowersMaureyIntervalMeasureScaled
import ThesisCommon.Analysis.GowersMaureyRISCutoff

/-! The RIS sum estimate of source Lemma 3, with the profile's analytic
properties exposed explicitly. The local form-norming condition is the
source's stated hypothesis; it is not a field of the constructed space.
The construction of the interpolating profiles of Lemma 6 remains separate. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem RISData.sum_norm_le_of_support {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (G : ℝ → ℝ) (g : ℕ → ℝ) {d : ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 0) G) (hmono : MonotoneOn G (Set.Ici 0))
    (hsmallG : ∀ t, 0 ≤ t → t ≤ 1 → G t = t) (hd : 0 ≤ d)
    (hsupport : ∀ u, 1 ≤ u → G u ≤ 1 + d * (u - 1))
    (hgap : 1 / (4 * Real.log 2) ≤ 1 - d)
    (hmul : ∀ r s, 0 ≤ r → 0 ≤ s → G r * G s ≤ G (r * s))
    (hg : ∀ k : ℕ, 2 ≤ k → Real.sqrt (logarithmicWeight k) ≤ g k)
    (hgprofile : ∀ k : ℕ, 1 ≤ k → (g k)⁻¹ * k = G k)
    (hnorm : ∀ E : Interval, ∀ r : ℝ, 1 ≤ r →
      r < implicitNorm D (GowersMaurey.restrict E (∑ i, x i)) →
      ∃ k : ℕ, 2 ≤ k ∧ ∃ a : C00 𝕜, IsForm D k (g k) a ∧
        r < ‖pairing a (GowersMaurey.restrict E (∑ i, x i))‖) :
    implicitNorm D (∑ i, x i) ≤ (1 + 2 * ε) * G N := by
  classical
  have hG0 : G 0 = 0 := hsmallG 0 le_rfl (by norm_num)
  have hG1 : G 1 = 1 := hsmallG 1 (by norm_num) le_rfl
  have hC : 1 ≤ 1 + 2 * ε := by linarith [h.epsilon_pos]
  have hGN0 : 0 ≤ G N := by
    rw [← hG0]
    exact hmono (by norm_num) (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N) (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)
  by_cases hN : N = 0
  · subst N
    simp [hG0]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let i0 : Fin N := ⟨0, hNpos⟩
  let n0 := h.size i0
  let y := ∑ i, x i
  have hyN : intervalNorm D n0 y ≤ N := h.intervalNorm_sum_le (fun i =>
    h.size_strict.monotone (by change 0 ≤ i.val; exact Nat.zero_le _))
  have hb : 0 ≤ (N : ℝ) / n0 := div_nonneg (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N) (Nat.cast_nonneg n0)
  have hb1 : (N : ℝ) / n0 ≤ 1 := h.size_ratio_le_one i0
  have hGN1 : 1 ≤ G N := by
    rw [← hG1]
    exact hmono (by norm_num) (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N) (by exact_mod_cast hNpos)
  have htarget1 : 1 ≤ (1 + 2 * ε) * G N :=
    hGN1.trans (le_mul_of_one_le_left hGN0 hC)
  by_cases hy0 : y = 0
  · change implicitNorm D y ≤ _
    rw [hy0, map_zero]
    exact zero_le_one.trans htarget1
  obtain ⟨μ, hμ, _, hμtotal, hμdom⟩ := exists_interval_measure_of_intervalNorm_le D
    (h.size_pos i0) (by exact_mod_cast hNpos : (0 : ℝ) < N) hy0 hyN
  have hgmin : ∀ k : ℕ, 2 ≤ k → Real.sqrt (logarithmicWeight 2) ≤ g k := by
    intro k hk
    exact (Real.sqrt_le_sqrt (logarithmicWeight_mono_nat hk)).trans (hg k hk)
  have hbudget : ∀ k : ℕ, 2 ≤ k → (k : ℝ) < risFormCutoff N ε →
      (k : ℝ) * ((N : ℝ) / n0) ≤ 1 - d := by
    intro k _ hk
    exact (h.small_form_budget i0 hk).trans hgap
  have hlarge : ∀ E : Interval, E.set ⊆ (supportInterval y).set → ∀ k : ℕ,
      2 ≤ k → risFormCutoff N ε ≤ k → ∀ a : C00 𝕜,
      IsForm D k (g k) a → ‖pairing a (GowersMaurey.restrict E y)‖ ≤ 1 + 2 * ε := by
    intro E _ k hk hkk a ha
    have hh := (h.restrict E).form_bound_of_large_size hk (hg k hk) ha hkk
    simpa only [y, map_sum] using hh
  have hbound := interval_norm_le_of_forms_and_measure D y (supportInterval y) G g
    hG hmono hsmallG hd hsupport hmul one_lt_sqrt_logarithmicWeight_two hgmin
    (fun k hk => hgprofile k (by omega)) hb hbudget hC μ hμ hμdom
    (fun E _ r hr hrv => hnorm E r hr hrv) hlarge
  by_cases hyb : (N : ℝ) / n0 < implicitNorm D y
  · have hh := hbound (supportInterval y) (Finset.Subset.refl _)
      (by simpa only [restrict_supportInterval] using hyb)
    simpa only [restrict_supportInterval, hμtotal] using hh
  · exact (le_of_not_gt hyb).trans (hb1.trans htarget1)

end ThesisCommon.GowersMaurey


