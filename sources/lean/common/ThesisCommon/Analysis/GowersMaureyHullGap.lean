import ThesisCommon.Analysis.GowersMaureyFactorCostGap
import ThesisCommon.Analysis.GowersMaureyFactorNormalization
import ThesisCommon.Analysis.FiniteFactorProductBounds

/-! A gap criterion for the actual finite-factor infimum. The finite list
enumerates only the preceding selected sizes, so its product can exploit
the genuine sparse growth rather than a factorial overestimate. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem interpolationHull_eq_weight_of_sparse_gap
    (K : Set ℕ) (hK : ∀ k ∈ K, 9 ≤ logarithmicWeight k)
    (r : List ℝ) (hr : r.Nodup) (hr1 : ∀ t ∈ r, 1 ≤ t)
    {x : ℝ} (hx : 1 ≤ x) (hsmall : r.prod ^ 2 ≤ Real.sqrt x)
    (hgap : ∀ k ∈ K, (k : ℝ) ∈ r ∨ logarithmicWeight x ≤ Real.sqrt (logarithmicWeight k)) :
    submultiplicativeHull (interpolationSeed K) x = logarithmicWeight x := by
  classical
  apply le_antisymm ((submultiplicativeHull_le (fun _ ht => interpolationSeed_ge_one K ht) hx).trans
    (interpolationSeed_bounds K hx).2)
  apply le_csInf (factorizationCosts_nonempty _ _)
  rintro a ⟨l, hl, hxl, rfl⟩
  obtain ⟨m, hm, hprod, hcost, hnorm⟩ := exists_normalized_interpolationSeed_factors K hK l hl
  apply le_trans ?_ hcost
  by_cases hbig : ∃ k ∈ K, (k : ℝ) ∈ m ∧
      logarithmicWeight x ≤ Real.sqrt (logarithmicWeight k)
  · obtain ⟨k, hk, hkm, hbig⟩ := hbig
    have hseed : interpolationSeed K k = Real.sqrt (logarithmicWeight k) :=
      if_pos ⟨k, hk, rfl⟩
    rw [← hseed] at hbig
    exact hbig.trans (list_factor_cost_ge_member (fun _ ht => interpolationSeed_ge_one K ht) hm hkm)
  · have hsub : selectedFactors K m ⊆ r := by
      intro t ht
      have htm := (List.mem_filter.mp ht).1
      obtain ⟨k, hk, rfl⟩ := of_decide_eq_true (List.mem_filter.mp ht).2
      rcases hgap k hk with hkr | hlarge
      · exact hkr
      · exact False.elim (hbig ⟨k, hk, htm, hlarge⟩)
    have hcount : ∀ t ∈ selectedFactors K m, (selectedFactors K m).count t ≤ 2 := by
      intro t ht
      have htK : t ∈ (fun k : ℕ => (k : ℝ)) '' K :=
        of_decide_eq_true (List.mem_filter.mp ht).2
      exact (List.Sublist.count_le t (List.filter_sublist)).trans (hnorm.2 t htK)
    apply factor_cost_ge_weight_of_small_selected_product K hm hx (by simpa only [hprod] using hxl)
    · intro t ht htK
      obtain ⟨k, hk, rfl⟩ := htK
      have hs := Real.sqrt_le_sqrt (hK k hk)
      norm_num at hs
      simpa only [interpolationSeed, if_pos (show (k : ℝ) ∈ (fun j : ℕ => (j : ℝ)) '' K from
        ⟨k, hk, rfl⟩)] using (show (2 : ℝ) ≤ Real.sqrt (logarithmicWeight k) by linarith)
    · exact (realList_prod_le_square_of_count_le_two _ r hr hsub hr1 hcount).trans hsmall

end ThesisCommon.GowersMaurey
