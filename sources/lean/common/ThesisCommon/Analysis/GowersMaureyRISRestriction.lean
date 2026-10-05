import ThesisCommon.Analysis.GowersMaureyRIS

/-! Restricting a genuine RIS to any interval preserves all its data,
including its support-range separation clauses. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem restrict_support_subset (E : Interval) (x : C00 𝕜) :
    (restrict E x).support ⊆ x.support := by
  classical
  intro n hn
  apply Finsupp.mem_support_iff.mpr
  have h := Finsupp.mem_support_iff.mp hn
  have h' : n ∈ E.set ∧ x n ≠ 0 := by
    simpa only [restrict_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] using h
  exact h'.2

theorem supportInterval_set_mono {a b : C00 𝕜} (hab : a.support ⊆ b.support) :
    (supportInterval a).set ⊆ (supportInterval b).set := by
  classical
  by_cases ha : a.support.Nonempty
  · have hb := ha.mono hab
    intro n hn
    rw [supportInterval, dif_pos ha] at hn
    rw [supportInterval, dif_pos hb]
    exact Finset.mem_Icc.mpr
      ⟨(Finset.min'_le _ _ (hab (Finset.min'_mem _ ha))).trans (Finset.mem_Icc.mp hn).1,
       (Finset.mem_Icc.mp hn).2.trans (Finset.le_max' _ _ (hab (Finset.max'_mem _ ha)))⟩
  · simp [supportInterval, ha]

theorem successive_restrict {N : ℕ} {x : Fin N → C00 𝕜} (hx : Successive x)
    (E : Interval) : Successive (fun i => restrict E (x i)) := by
  intro i j hij s hs t ht
  exact hx i j hij s (restrict_support_subset E (x i) hs) t (restrict_support_subset E (x j) ht)

theorem prefixSum_restrict {N : ℕ} (x : Fin N → C00 𝕜) (E : Interval) (i : Fin N) :
    prefixSum (fun j => restrict E (x j)) i = restrict E (prefixSum x i) := by
  simp [prefixSum]

def RISData.restrict {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ} {x : Fin N → C00 𝕜}
    (h : RISData D ε x) (E : Interval) : RISData D ε (fun i => GowersMaurey.restrict E (x i)) where
  epsilon_pos := h.epsilon_pos
  epsilon_le_one := h.epsilon_le_one
  successive := successive_restrict h.successive E
  size := h.size
  size_strict := h.size_strict
  size_pos := h.size_pos
  first_large := h.first_large
  norm_bound i := (intervalNorm_restrict_le D (h.size i) E (x i)).trans (h.norm_bound i)
  spacing i hi := by
    rw [prefixSum_restrict]
    apply lt_of_le_of_lt _ (h.spacing i hi)
    exact_mod_cast Finset.card_le_card (supportInterval_set_mono
      (restrict_support_subset E (prefixSum x i)))

theorem IsRIS.restrict {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ} {x : Fin N → C00 𝕜}
    (h : IsRIS D ε x) (E : Interval) : IsRIS D ε (fun i => restrict E (x i)) := by
  obtain ⟨h⟩ := h
  exact ⟨h.restrict E⟩

end ThesisCommon.GowersMaurey
