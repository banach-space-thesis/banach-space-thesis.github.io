import ThesisCommon.Analysis.QuotientRealMeasure

/-! The real local-scalar argument of Drewnowski--Roberts, Lemma 2.3,
implemented on actual quotient classes and free-ultrafilter evaluations. -/
noncomputable section
open Filter Set
namespace ThesisCommon.QuotientRealMeasure
attribute [local instance] Classical.propDecidable

theorem stable_positive_neg_upper_zero (μ : QuotientRealMeasure) {B : Set ℕ}
    (hB : B.Infinite)
    (hstable : ∀ C : Set ℕ, C.Infinite → C ⊆ B → μ.upper C = μ.upper B)
    (hnegstable : ∀ C : Set ℕ, C.Infinite → C ⊆ B → μ.neg.upper C = μ.neg.upper B)
    (hpos : 0 < μ.upper B) : μ.neg.upper B = 0 := by
  apply le_antisymm _ (μ.neg.upper_nonneg hB)
  by_contra hnot
  have hneg : 0 < μ.neg.upper B := lt_of_not_ge hnot
  let ε := min (μ.upper B) (μ.neg.upper B) / 8
  have hε : 0 < ε := div_pos (lt_min hpos hneg) (by norm_num)
  have hεβ : 8 * ε ≤ μ.upper B := by dsimp [ε]; linarith [min_le_left (μ.upper B) (μ.neg.upper B)]
  have hεα : 8 * ε ≤ μ.neg.upper B := by dsimp [ε]; linarith [min_le_right (μ.upper B) (μ.neg.upper B)]
  obtain ⟨F, hFB, U, hUB, hFU⟩ := μ.exists_eval_gt hB (show μ.upper B - ε < μ.upper B by linarith)
  obtain ⟨H, hHB, hH, hHF⟩ := μ.localize F U hUB hFU
  have hfin : (H \ F).Finite := by
    by_contra hfin
    have hHI : (H \ F).Infinite := hfin
    have hs := hstable (H \ F) hHI (diff_subset.trans hHB)
    obtain ⟨G, hGH, V, hVH, hGV⟩ := μ.exists_eval_gt hHI
      (show μ.upper B - ε < μ.upper (H \ F) by rw [hs]; linarith)
    have hVH' : H ∈ V := Filter.mem_of_superset hVH diff_subset
    have hFV := hHF V hVH'
    have hd : Disjoint F G := disjoint_left.mpr (by
      intro n hnF hnG
      exact (hGH hnG).2 hnF)
    have hu := μ.eval_le_upper (union_subset hFB (hGH.trans (diff_subset.trans hHB))) V
      (Filter.mem_of_superset hVH' hHB)
    rw [μ.eval_union hd] at hu
    linarith
  let H' := H \ (H \ F)
  have hH' : H'.Infinite := hH.diff hfin
  have hH'H : H' ⊆ H := diff_subset
  have hH'F : H' ⊆ F := by
    intro n hn
    exact Classical.byContradiction (fun hnF => hn.2 ⟨hn.1, hnF⟩)
  have hs := hnegstable H' hH' (hH'H.trans hHB)
  obtain ⟨G, hGH, V, hVH, hGV⟩ := μ.neg.exists_eval_gt hH'
    (show μ.neg.upper B - ε < μ.neg.upper H' by rw [hs]; linarith)
  have hFV := hHF V (Filter.mem_of_superset hVH hH'H)
  have hu := μ.eval_le_upper (diff_subset.trans hFB : F \ G ⊆ B) V
    (Filter.mem_of_superset hVH (hH'H.trans hHB))
  rw [μ.eval_sdiff (hGH.trans hH'F)] at hu
  rw [eval_neg] at hGV
  linarith

theorem stable_nonnegative_scalar (μ : QuotientRealMeasure) {B : Set ℕ}
    (_hB : B.Infinite)
    (hstable : ∀ C : Set ℕ, C.Infinite → C ⊆ B → μ.upper C = μ.upper B)
    (hpos : ∀ F : Set ℕ, F ⊆ B → ∀ U : FreeNatUltrafilter, B ∈ U → 0 ≤ μ.eval F U) :
    ∀ F : Set ℕ, F ⊆ B → ∀ U : FreeNatUltrafilter, B ∈ U →
      μ.eval F U = if F ∈ U then μ.upper B else 0 := by
  intro F hFB U hUB
  have hupper := μ.eval_le_upper hFB U hUB
  by_cases hFU : F ∈ U
  · rw [if_pos hFU]
    apply le_antisymm hupper
    by_contra hnot
    have hlt : μ.eval F U < μ.upper B := lt_of_not_ge hnot
    let a := (μ.upper B - μ.eval F U) / 2
    have ha : 0 < a := by dsimp [a]; linarith
    have hlow : -(μ.upper B - a) < μ.neg.eval F U := by
      rw [eval_neg]
      dsimp [a]
      linarith
    obtain ⟨H, hHF, hH, hHV⟩ := μ.neg.localize F U hFU hlow
    have hs := hstable H hH (hHF.trans hFB)
    obtain ⟨G, hGH, V, hVH, hGV⟩ := μ.exists_eval_gt hH
      (show μ.upper B - a < μ.upper H by rw [hs]; linarith)
    have hFV := hHV V hVH
    rw [eval_neg] at hFV
    have hp := hpos (F \ G) (diff_subset.trans hFB) V
      (Filter.mem_of_superset hVH (hHF.trans hFB))
    rw [μ.eval_sdiff (hGH.trans hHF)] at hp
    linarith
  · rw [if_neg hFU]
    apply le_antisymm _ (hpos F hFB U hUB)
    by_contra hnot
    have hlt : 0 < μ.eval F U := lt_of_not_ge hnot
    have hdiff : B \ F ∈ U := Filter.inter_mem hUB
      (U.val.compl_mem_iff_notMem.mpr hFU)
    obtain ⟨H, hHF, hH, hHV⟩ := μ.localize F U hdiff (half_lt_self hlt)
    have hs := hstable H hH (hHF.trans diff_subset)
    obtain ⟨G, hGH, V, hVH, hGV⟩ := μ.exists_eval_gt hH
      (show μ.upper B - μ.eval F U / 2 < μ.upper H by rw [hs]; linarith)
    have hFV := hHV V hVH
    have hd : Disjoint F G := disjoint_left.mpr (by
      intro n hnF hnG
      exact (hHF (hGH hnG)).2 hnF)
    have hu := μ.eval_le_upper (union_subset hFB (hGH.trans (hHF.trans diff_subset))) V
      (Filter.mem_of_superset hVH (hHF.trans diff_subset))
    rw [μ.eval_union hd] at hu
    linarith

theorem exists_scalar_subset (μ : QuotientRealMeasure) {A : Set ℕ} (hA : A.Infinite) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∃ c : ℝ,
      ∀ F : Set ℕ, F ⊆ B → ∀ U : FreeNatUltrafilter, B ∈ U →
        μ.eval F U = if F ∈ U then c else 0 := by
  obtain ⟨A', hA', hA'A, hstable⟩ := μ.exists_stable_upper hA
  obtain ⟨B, hB, hBA', hnegstable⟩ := μ.neg.exists_stable_upper hA'
  have hstableB : ∀ C : Set ℕ, C.Infinite → C ⊆ B → μ.upper C = μ.upper B := by
    intro C hC hCB
    rw [hstable C hC (hCB.trans hBA'), hstable B hB hBA']
  by_cases hβ : 0 < μ.upper B
  · have hα := μ.stable_positive_neg_upper_zero hB hstableB hnegstable hβ
    refine ⟨B, hB, hBA'.trans hA'A, μ.upper B, μ.stable_nonnegative_scalar hB hstableB ?_⟩
    intro F hFB U hUB
    have h := μ.neg.eval_le_upper hFB U hUB
    rw [eval_neg, hα] at h
    linarith
  · have hβ0 : μ.upper B = 0 := le_antisymm (le_of_not_gt hβ) (μ.upper_nonneg hB)
    have hp : ∀ F : Set ℕ, F ⊆ B → ∀ U : FreeNatUltrafilter, B ∈ U → 0 ≤ μ.neg.eval F U := by
      intro F hFB U hUB
      have h := μ.eval_le_upper hFB U hUB
      rw [hβ0] at h
      rw [eval_neg]
      linarith
    refine ⟨B, hB, hBA'.trans hA'A, -μ.neg.upper B, ?_⟩
    intro F hFB U hUB
    have h := μ.neg.stable_nonnegative_scalar hB hnegstable hp F hFB U hUB
    rw [eval_neg] at h
    split_ifs at h ⊢ <;> linarith

end ThesisCommon.QuotientRealMeasure
