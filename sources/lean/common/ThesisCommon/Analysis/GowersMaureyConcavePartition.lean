import ThesisCommon.Analysis.GowersMaureyConcaveSum

/-! The finite partition version of the numerical induction estimate in
source Lemma 3. The zero number of large pieces is included. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey

theorem concave_partition_sum_estimate {G : ℝ → ℝ} {d : ℝ}
    (hG : ConcaveOn ℝ (Set.Ici 0) G) (hmono : MonotoneOn G (Set.Ici 0))
    (hG1 : G 1 = 1) (hd : 0 ≤ d)
    (hsupport : ∀ u, 1 ≤ u → G u ≤ 1 + d * (u - 1))
    (hmul : ∀ r s, 0 ≤ r → 0 ≤ s → G r * G s ≤ G (r * s))
    {k : ℕ} {α b C w : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hαk : α * k = G k)
    (hb : 0 ≤ b) (hkb : (k : ℝ) * b ≤ 1 - d) (hC : 1 ≤ C) (hw : 1 ≤ w)
    (u y : Fin k → ℝ) (hu : ∀ i, 0 ≤ u i) (hsum : (∑ i, u i) ≤ w)
    (A : Finset (Fin k)) (hsmall : ∀ i ∈ A, y i ≤ b)
    (hlarge : ∀ i, i ∉ A → y i ≤ C * G (u i)) :
    α * (∑ i, y i) ≤ C * G w := by
  classical
  let B := Finset.univ \ A
  have hC0 : 0 ≤ C := by linarith
  have hA : (∑ i ∈ A, y i) ≤ (A.card : ℝ) * b := by
    simpa using Finset.sum_le_sum hsmall
  by_cases hB : B.Nonempty
  · have hm : 0 < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB
    have hcard : (k : ℝ) = (B.card : ℝ) + A.card := by
      have hcardnat : k = B.card + A.card := by
        simpa [B] using (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)).symm
      exact_mod_cast hcardnat
    have hsumB : (∑ i ∈ B, u i) ≤ w :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (fun i _ _ => hu i)).trans hsum
    have hBbound : (∑ i ∈ B, y i) ≤ C * B.card * G (w / B.card) := by
      calc
        _ ≤ ∑ i ∈ B, C * G (u i) := Finset.sum_le_sum fun i hi =>
          hlarge i (Finset.mem_sdiff.mp hi).2
        _ = C * ∑ i ∈ B, G (u i) := (Finset.mul_sum _ _ _).symm
        _ ≤ C * ((B.card : ℝ) * G (w / B.card)) := mul_le_mul_of_nonneg_left
          (concave_sum_le_card_mul hG hmono B hB u (fun i _ => hu i) hsumB) hC0
        _ = _ := by ring
    have hsplit : (∑ i, y i) = (∑ i ∈ A, y i) + ∑ i ∈ B, y i := by
      have h := Finset.sum_sdiff (f := y) (Finset.subset_univ A)
      simpa only [B, add_comm] using h.symm
    calc
      α * (∑ i, y i) ≤ α * ((A.card : ℝ) * b + C * B.card * G (w / B.card)) := by
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left (add_le_add hA hBbound) hα
      _ ≤ C * G w := concave_two_class_estimate hG hG1 hsupport hmul
        (Nat.cast_nonneg A.card) hm hcard hα1 hαk hb hkb hC hw
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    have hAu : A = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hi
      have hiB : i ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
      rw [he] at hiB
      exact Finset.notMem_empty _ hiB
    have hsumy : (∑ i, y i) ≤ (k : ℝ) * b := by simpa [hAu] using hA
    have hGw : 1 ≤ G w := by
      rw [← hG1]
      exact hmono (by norm_num) (by change 0 ≤ w; linarith) hw
    calc
      α * (∑ i, y i) ≤ α * ((k : ℝ) * b) := mul_le_mul_of_nonneg_left hsumy hα
      _ ≤ (k : ℝ) * b := mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg k) hb) hα1
      _ ≤ 1 - d := hkb
      _ ≤ 1 := by linarith
      _ ≤ C * G w := hGw.trans (le_mul_of_one_le_left (by linarith) hC)

end ThesisCommon.GowersMaurey
