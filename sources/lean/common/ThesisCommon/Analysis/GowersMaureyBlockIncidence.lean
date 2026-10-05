import ThesisCommon.Analysis.GowersMaureyBlockSums
import ThesisCommon.Analysis.FiniteMonotoneIncidence

/-! The actual interval norm of a sum of small successive blocks. Nonzero
interval/block intersections form a noncrossing incidence family. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_support_mem_of_restrict_ne_zero {E : Interval} {x : C00 𝕜}
    (h : restrict E x ≠ 0) : ∃ n, n ∈ E.set ∧ n ∈ x.support := by
  classical
  obtain ⟨n, hn⟩ := Finsupp.support_nonempty_iff.mpr h
  have hne := Finsupp.mem_support_iff.mp hn
  rw [restrict_apply] at hne
  have hE : n ∈ E.set := by
    by_contra hh
    simp [hh] at hne
  exact ⟨n, hE, Finsupp.mem_support_iff.mpr (by simpa only [if_pos hE] using hne)⟩

theorem intervalSum_successive_bound (D : ConstructionData 𝕜) {N m : ℕ}
    (I : FiniteIntervalFamily N) {x : Fin m → C00 𝕜} (hx : Successive x)
    {b : ℝ} (hb : 0 ≤ b) (hbound : ∀ i, implicitNorm D (x i) ≤ b) :
    intervalSum D I (∑ i, x i) ≤ ((N + m : ℕ) : ℝ) * b := by
  classical
  let s := Finset.univ.filter (fun a : Fin N × Fin m => restrict (I.interval a.1) (x a.2) ≠ 0)
  have hs : s.card ≤ N + m := by
    apply card_monotone_incidence_le
    intro a ha c hc hac
    by_contra hbad
    have hrev : c.2 < a.2 := lt_of_not_ge hbad
    obtain ⟨u, huE, hux⟩ := exists_support_mem_of_restrict_ne_zero (Finset.mem_filter.mp ha).2
    obtain ⟨v, hvE, hvx⟩ := exists_support_mem_of_restrict_ne_zero (Finset.mem_filter.mp hc).2
    have huv := I.successive a.1 c.1 hac u huE v hvE
    have hvu := hx c.2 a.2 hrev v hvx u hux
    omega
  have hsum : (∑ a ∈ s, implicitNorm D (restrict (I.interval a.1) (x a.2))) =
      ∑ a : Fin N × Fin m, implicitNorm D (restrict (I.interval a.1) (x a.2)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs with ha
    · rfl
    · simp only [not_not] at ha
      simp [ha]
  calc
    intervalSum D I (∑ i, x i) = ∑ j, implicitNorm D (∑ i, restrict (I.interval j) (x i)) := by
      simp only [intervalSum_apply, map_sum]
    _ ≤ ∑ j, ∑ i, implicitNorm D (restrict (I.interval j) (x i)) :=
      Finset.sum_le_sum fun j _ => seminorm_sum_le _ _ _
    _ = ∑ a : Fin N × Fin m, implicitNorm D (restrict (I.interval a.1) (x a.2)) := by
      symm
      exact Fintype.sum_prod_type _
    _ = ∑ a ∈ s, implicitNorm D (restrict (I.interval a.1) (x a.2)) := hsum.symm
    _ ≤ ∑ _a ∈ s, b := Finset.sum_le_sum fun a _ =>
      (implicitNorm_restrict_le D _ _).trans (hbound a.2)
    _ = (s.card : ℝ) * b := by simp
    _ ≤ ((N + m : ℕ) : ℝ) * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hb

theorem intervalNorm_successive_sum_bound (D : ConstructionData 𝕜) (N : ℕ) {m : ℕ}
    {x : Fin m → C00 𝕜} (hx : Successive x) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i, implicitNorm D (x i) ≤ b) :
    intervalNorm D N (∑ i, x i) ≤ ((N + m : ℕ) : ℝ) * b := by
  rw [intervalNorm, Seminorm.sSup_apply (intervalSums_bddAbove D N)]
  apply ciSup_le
  rintro ⟨_, I, rfl⟩
  exact intervalSum_successive_bound D I hx hb hbound

end ThesisCommon.GowersMaurey
