import ThesisCommon.Analysis.GowersMaureyFactorCostBounds

/-! The central finite-cost inequality in the interpolation gap proof.
If the product of the selected factors is at most sqrt(x), then the
remaining factors have product at least sqrt(x). A selected factor of
cost at least two supplies exactly the logarithmic loss. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

def selectedFactors (K : Set ℕ) (l : List ℝ) : List ℝ := by
  classical
  exact l.filter (fun t => t ∈ (fun k : ℕ => (k : ℝ)) '' K)

theorem factor_cost_ge_weight_of_small_selected_product (K : Set ℕ)
    {l : List ℝ} (hl : ∀ t ∈ l, 1 ≤ t) {x : ℝ} (hx : 1 ≤ x) (hprod : x ≤ l.prod)
    (hselected : ∀ t ∈ l, t ∈ (fun k : ℕ => (k : ℝ)) '' K → 2 ≤ interpolationSeed K t)
    (hsmall : (selectedFactors K l).prod ≤ Real.sqrt x) :
    logarithmicWeight x ≤ (l.map (interpolationSeed K)).prod := by
  classical
  let P : ℝ → Prop := fun t => t ∈ (fun k : ℕ => (k : ℝ)) '' K
  let s := l.filter P
  let u := l.filter (fun t => ¬ P t)
  have hs : ∀ t ∈ s, 1 ≤ t := fun t ht => hl t (List.mem_filter.mp ht).1
  have hu : ∀ t ∈ u, 1 ≤ t := fun t ht => hl t (List.mem_filter.mp ht).1
  have hsplit : s.prod * u.prod = l.prod := by
    simpa only [List.map_id] using list_filter_cost_partition id P l
  have hcost : (s.map (interpolationSeed K)).prod * (u.map (interpolationSeed K)).prod =
      (l.map (interpolationSeed K)).prod := list_filter_cost_partition (interpolationSeed K) P l
  have huCost : (u.map (interpolationSeed K)).prod = (u.map logarithmicWeight).prod := by
    congr 1
    apply List.map_congr_left
    intro t ht
    have hnot : ¬ P t := of_decide_eq_true (List.mem_filter.mp ht).2
    exact if_neg hnot
  have huLower : logarithmicWeight u.prod ≤ (u.map (interpolationSeed K)).prod := by
    rw [huCost]
    exact list_logarithmicWeight_prod_le hu
  by_cases hs0 : s = []
  · have hxu : x ≤ u.prod := by
      rw [← hsplit, hs0, List.prod_nil, one_mul] at hprod
      exact hprod
    have hh := logarithmicWeight_strictMonoOn.monotoneOn hx (list_prod_ge_one hu) hxu
    have hfinal := hh.trans huLower
    have hc : (u.map (interpolationSeed K)).prod = (l.map (interpolationSeed K)).prod := by
      simpa only [hs0, List.map_nil, List.prod_nil, one_mul] using hcost
    exact hfinal.trans_eq hc
  · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil s hs0
    have htwo : 2 ≤ (s.map (interpolationSeed K)).prod :=
      (hselected a (List.mem_filter.mp ha).1 (of_decide_eq_true (List.mem_filter.mp ha).2)).trans
        (list_factor_cost_ge_member (fun _ ht => interpolationSeed_ge_one K ht) hs ha)
    have hroot : Real.sqrt x ≤ u.prod := sqrt_le_factor_of_small_other_product hx
      (zero_le_one.trans (list_prod_ge_one hu))
      (by rw [← hsplit] at hprod; simpa only [mul_comm] using hprod) hsmall
    have hroot1 : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
    have hrootCost : logarithmicWeight (Real.sqrt x) ≤ (u.map (interpolationSeed K)).prod :=
      (logarithmicWeight_strictMonoOn.monotoneOn hroot1 (list_prod_ge_one hu) hroot).trans huLower
    calc
      logarithmicWeight x ≤ 2 * logarithmicWeight (Real.sqrt x) := logarithmicWeight_le_twice_sqrt (zero_le_one.trans hx)
      _ ≤ (s.map (interpolationSeed K)).prod * (u.map (interpolationSeed K)).prod :=
        mul_le_mul htwo hrootCost (zero_le_one.trans (one_le_logarithmicWeight_real hroot1))
          (by linarith)
      _ = _ := hcost

end ThesisCommon.GowersMaurey
