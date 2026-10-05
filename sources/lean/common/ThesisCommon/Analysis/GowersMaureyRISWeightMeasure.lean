import ThesisCommon.Analysis.GowersMaureyRISAdmissibleProfile

/-! A single finite weight measure controls all interval restrictions of
an RIS sum. This retains the small-interval remainder needed in Lemma 7,
instead of discarding the measure after estimating the whole vector. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem RISData.exists_weight_measure {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) (G : ℝ → ℝ) (g : ℕ → ℝ) {d : ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 0) G) (hmono : MonotoneOn G (Set.Ici 0))
    (hsmallG : ∀ t, 0 ≤ t → t ≤ 1 → G t = t) (hd : 0 ≤ d)
    (hderiv : HasDerivWithinAt G d (Set.Ioi 1) 1)
    (hgap : 1 / (4 * Real.log 2) ≤ 1 - d)
    (hmul : ∀ r s, 0 ≤ r → 0 ≤ s → G r * G s ≤ G (r * s))
    (hg : ∀ k : ℕ, 2 ≤ k → Real.sqrt (logarithmicWeight k) ≤ g k)
    (hgf : ∀ k : ℕ, 2 ≤ k → g k ≤ logarithmicWeight k)
    (hgspecial : ∀ k, k ∈ D.specialSizes → g k ≤ Real.sqrt (logarithmicWeight k))
    (hgprofile : ∀ k : ℕ, 1 ≤ k → (g k)⁻¹ * k = G k)
    (i0 : Fin N) (hmin : ∀ i, h.size i0 ≤ h.size i)
    (hx0 : (∑ i, x i) ≠ 0) :
    ∃ μ : ℕ → ℝ, (∀ n, 0 ≤ μ n) ∧
      (∀ n, n ∉ (supportInterval (∑ i, x i)).set → μ n = 0) ∧
      (∑ n ∈ (supportInterval (∑ i, x i)).set, μ n) = N ∧
      ∀ E : Interval, E.set ⊆ (supportInterval (∑ i, x i)).set →
        implicitNorm D (GowersMaurey.restrict E (∑ i, x i)) ≤
          (1 + 2 * ε) * (G (∑ n ∈ E.set, μ n) + (N : ℝ) / h.size i0) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i0.val) i0.isLt
  have hG0 : G 0 = 0 := hsmallG 0 le_rfl (by norm_num)
  have hG1 : G 1 = 1 := hsmallG 1 (by norm_num) le_rfl
  have hC : 1 ≤ 1 + 2 * ε := by linarith [h.epsilon_pos]
  have hb : 0 ≤ (N : ℝ) / h.size i0 := div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg _)
  have hgpos : ∀ k, 2 ≤ k → 0 < g k := by
    intro k hk
    exact (Real.sqrt_pos.mpr (zero_lt_one.trans_le
      (one_le_logarithmicWeight (by omega)))).trans_le (hg k hk)
  obtain ⟨μ, hμ, hμsupp, hμtotal, hμdom⟩ := exists_interval_measure_of_intervalNorm_le D
    (h.size_pos i0) (by exact_mod_cast hN : (0 : ℝ) < N) hx0 (h.intervalNorm_sum_le hmin)
  have hG' : ConcaveOn ℝ (Set.Ici 1) G := hG.subset
    (by intro u hu; change 0 ≤ u; exact zero_le_one.trans (show 1 ≤ u from hu)) (convex_Ici 1)
  have hsupport := concave_support_of_right_derivative hG' hG1 hderiv
  have hgmin : ∀ k : ℕ, 2 ≤ k → Real.sqrt (logarithmicWeight 2) ≤ g k := by
    intro k hk
    exact (Real.sqrt_le_sqrt (logarithmicWeight_mono_nat hk)).trans (hg k hk)
  have hbudget : ∀ k : ℕ, 2 ≤ k → (k : ℝ) < risFormCutoff N ε →
      (k : ℝ) * ((N : ℝ) / h.size i0) ≤ 1 - d := by
    intro k _ hk
    exact (h.small_form_budget i0 hk).trans hgap
  have hlarge : ∀ E : Interval, E.set ⊆ (supportInterval (∑ i, x i)).set → ∀ k : ℕ,
      2 ≤ k → risFormCutoff N ε ≤ k → ∀ a : C00 𝕜,
      IsForm D k (g k) a → ‖pairing a (GowersMaurey.restrict E (∑ i, x i))‖ ≤ 1 + 2 * ε := by
    intro E _ k hk hkk a ha
    simpa only [map_sum] using (h.restrict E).form_bound_of_large_size hk (hg k hk) ha hkk
  have hbound := interval_norm_le_of_forms_and_measure D (∑ i, x i)
    (supportInterval (∑ i, x i)) G g hG hmono hsmallG hd hsupport hmul
    one_lt_sqrt_logarithmicWeight_two hgmin (fun k hk => hgprofile k (by omega))
    hb hbudget hC μ hμ hμdom
    (fun E _ r hr hn => h.exists_norming_form g hgpos hgf hgspecial E hr hn) hlarge
  refine ⟨μ, hμ, hμsupp, hμtotal, ?_⟩
  intro E hE
  have hw : 0 ≤ ∑ n ∈ E.set, μ n := Finset.sum_nonneg fun n _ => hμ n
  have hGw : 0 ≤ G (∑ n ∈ E.set, μ n) := by
    rw [← hG0]
    exact hmono (by norm_num) hw hw
  by_cases hbig : (N : ℝ) / h.size i0 < implicitNorm D (GowersMaurey.restrict E (∑ i, x i))
  · exact (hbound E hE hbig).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hb)
      (zero_le_one.trans hC))
  · exact (le_of_not_gt hbig).trans ((le_mul_of_one_le_left hb hC).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hGw) (zero_le_one.trans hC)))

end ThesisCommon.GowersMaurey
