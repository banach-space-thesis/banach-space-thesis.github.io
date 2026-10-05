import ThesisCommon.Analysis.JamesBlockPaths
import ThesisCommon.Analysis.JamesPathJoins

/-! The lower lp estimate for consecutive finite James blocks. Paths in
adjacent intervals are joined through their common zero boundary, so no
factor depending on the number or lengths of the blocks is introduced. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem james_window_paths_join (σ : ℕ → ℕ) {n : ℕ} (s : Fin n → JamesPath)
    (hl : ∀ i, σ i.val ≤ (s i).index 0)
    (hr : ∀ i, (s i).index (Fin.last (s i).length) ≤ σ (i.val + 1)) (a : ℕ → 𝕜) :
    ∃ u : JamesPath, u.index (Fin.last u.length) ≤ σ n ∧
      (∑ i : Fin n, ‖jamesRawPath p (s i) a‖ ^ p.val.toReal) ≤
        ‖jamesRawPath p u a‖ ^ p.val.toReal := by
  induction n with
  | zero =>
    refine ⟨JamesPath.point (σ 0), le_rfl, ?_⟩
    exact (by simp only [Fin.sum_univ_zero]; positivity)
  | succ n ih =>
    obtain ⟨u, hu, he⟩ := ih (fun i => s i.castSucc)
      (fun i => hl i.castSucc) (fun i => hr i.castSucc)
    obtain ⟨v, hv, hbound⟩ := jamesPath_join_energy p hp u (s (Fin.last n))
      (hu.trans (hl (Fin.last n))) a
    refine ⟨v, hv.trans_le (hr (Fin.last n)), ?_⟩
    rw [Fin.sum_univ_castSucc]
    exact (add_le_add_right he _).trans hbound

include hp in
theorem james_window_paths_energy_le (σ : ℕ → ℕ) {n : ℕ} (s : Fin n → JamesPath)
    (hl : ∀ i, σ i.val ≤ (s i).index 0)
    (hr : ∀ i, (s i).index (Fin.last (s i).length) ≤ σ (i.val + 1))
    (x : JamesSequenceSpace 𝕜 p) :
    (∑ i : Fin n, ‖jamesPathMap 𝕜 p (s i) x.val‖ ^ p.val.toReal) ≤ ‖x‖ ^ p.val.toReal := by
  obtain ⟨u, _, hu⟩ := james_window_paths_join p hp σ s hl hr (fun k => x k)
  exact hu.trans (Real.rpow_le_rpow (norm_nonneg _) (x.path_norm_le u) ENNReal.toReal_nonneg)

theorem james_finite_blocks_sum_on_interval (σ : ℕ → ℕ) (hσ : StrictMono σ) {n : ℕ}
    (x : ∀ i : Fin n, JamesIntervalBlock 𝕜 p (σ i.val) (σ (i.val + 1)))
    (i : Fin n) (k : ℕ) (hl : σ i.val ≤ k) (hr : k ≤ σ (i.val + 1)) :
    (∑ j : Fin n, (x j).val) k = (x i).val k := by
  classical
  change JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) k (∑ j : Fin n, (x j).val) = _
  rw [map_sum]
  apply Finset.sum_eq_single i
  · intro j _ hji
    change (x j).val k = 0
    rcases lt_or_gt_of_ne hji with hji | hij
    · exact (x j).property k (Or.inr ((hσ.monotone (by exact_mod_cast hji)).trans hl))
    · exact (x j).property k (Or.inl (hr.trans (hσ.monotone (by exact_mod_cast hij))))
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

include hp in
theorem james_finite_blocks_lower (σ : ℕ → ℕ) (hσ : StrictMono σ) {n : ℕ}
    (x : ∀ i : Fin n, JamesIntervalBlock 𝕜 p (σ i.val) (σ (i.val + 1))) :
    (∑ i : Fin n, ‖x i‖ ^ p.val.toReal) ≤ ‖∑ i : Fin n, (x i).val‖ ^ p.val.toReal := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / ((n : ℝ) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : (n : ℝ) * δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr (by nlinarith)
  have hex (i : Fin n) : ∃ s : JamesPath, σ i.val ≤ s.index 0 ∧
      s.index (Fin.last s.length) ≤ σ (i.val + 1) ∧
      ‖x i‖ ^ p.val.toReal - δ < ‖jamesPathMap 𝕜 p s (x i).val.val‖ ^ p.val.toReal :=
    jamesIntervalBlock_exists_path_gt p hp (hσ.monotone (by omega)) (x i) (by linarith)
  choose s hl hr hs using hex
  let z : JamesSequenceSpace 𝕜 p := ∑ i : Fin n, (x i).val
  have hpath (i : Fin n) : jamesPathMap 𝕜 p (s i) z.val =
      jamesPathMap 𝕜 p (s i) (x i).val.val := by
    ext j
    change z ((s i).index j.castSucc) - z ((s i).index j.succ) = _
    rw [james_finite_blocks_sum_on_interval p σ hσ x i _
      ((hl i).trans ((s i).strictMono.monotone (Fin.zero_le _)))
      (((s i).strictMono.monotone (Fin.le_last _)).trans (hr i)),
      james_finite_blocks_sum_on_interval p σ hσ x i _
      ((hl i).trans ((s i).strictMono.monotone (Fin.zero_le _)))
      (((s i).strictMono.monotone (Fin.le_last _)).trans (hr i))]
    rfl
  have henergy : (∑ i : Fin n, ‖jamesPathMap 𝕜 p (s i) (x i).val.val‖ ^ p.val.toReal) ≤
      ‖z‖ ^ p.val.toReal := by
    simpa only [hpath] using james_window_paths_energy_le p hp σ s hl hr z
  calc
    _ ≤ ∑ i : Fin n, (‖jamesPathMap 𝕜 p (s i) (x i).val.val‖ ^ p.val.toReal + δ) :=
      Finset.sum_le_sum (fun i _ => by linarith [hs i])
    _ = (∑ i : Fin n, ‖jamesPathMap 𝕜 p (s i) (x i).val.val‖ ^ p.val.toReal) + (n : ℝ) * δ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ‖z‖ ^ p.val.toReal + ε := add_le_add henergy hsmall

end ThesisCommon
