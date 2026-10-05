import ThesisCommon.Analysis.EllOneSchurBlocks

/-! A single bounded scalar test detects all members of a disjoint block
subsequence. This is the contradiction behind Schur's theorem. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ThesisCommon
variable {I : Type*}
attribute [local instance] Classical.decEq Classical.propDecidable

private def blockSign (u : ℕ → lp (fun _ : I => ℝ) 1) (B : ℕ → Finset I) (i : I) : ℝ :=
  if h : ∃ n, i ∈ B n then if 0 ≤ u h.choose i then 1 else -1 else 0

private theorem blockSign_bound (u : ℕ → lp (fun _ : I => ℝ) 1)
    (B : ℕ → Finset I) (i : I) : |blockSign u B i| ≤ 1 := by
  unfold blockSign
  split_ifs <;> norm_num

private theorem blockSign_mul (u : ℕ → lp (fun _ : I => ℝ) 1)
    (B : ℕ → Finset I) (hB : Pairwise (fun m n => Disjoint (B m) (B n)))
    (n : ℕ) (i : I) (hi : i ∈ B n) : blockSign u B i * u n i = ‖u n i‖ := by
  have h : ∃ m, i ∈ B m := ⟨n, hi⟩
  have heq : h.choose = n := by
    by_contra hn
    exact Finset.disjoint_left.mp (hB hn) h.choose_spec hi
  rw [blockSign, dif_pos h, heq, Real.norm_eq_abs]
  split_ifs with hpos
  · rw [one_mul, abs_of_nonneg hpos]
  · rw [neg_one_mul, abs_of_neg (lt_of_not_ge hpos)]

/-- A coordinatewise null sequence has a subsequence and a norm-at-most-one
scalar test whose evaluations are within `2ε` below the sequence norms. -/
theorem ellOne_subsequence_norm_test (u : ℕ → lp (fun _ : I => ℝ) 1)
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ φ : lp (fun _ : I => ℝ) 1 →L[ℝ] ℝ,
      ∀ n, ‖u (r n)‖ - 2 * ε < φ (u (r n)) := by
  obtain ⟨r, hr, B, hB, herr⟩ := ellOne_disjoint_finite_blocks u hu hε
  let v := fun n => u (r n)
  let b := blockSign v B
  have hb := blockSign_bound v B
  let φ := ellOneTest b hb
  refine ⟨r, hr, φ, fun n => ?_⟩
  let w := ∑ i ∈ B n, lp.single 1 i (v n i)
  have hw : φ w = ∑ i ∈ B n, ‖v n i‖ := by
    simp only [w, map_sum, φ, ellOneTest_single]
    exact Finset.sum_congr rfl (fun i hi => blockSign_mul v B hB n i hi)
  have ht := (abs_le.mp (ellOneTest_bound b hb (v n - w))).1
  change -‖v n - w‖ ≤ φ (v n - w) at ht
  rw [map_sub, hw] at ht
  have he := herr n
  have hn := ellOne_norm_tail (v n) (B n)
  change ‖v n - w‖ = ‖v n‖ - ∑ i ∈ B n, ‖v n i‖ at hn
  change ‖v n - w‖ < ε at he
  change ‖v n‖ - 2 * ε < φ (v n)
  linarith

end ThesisCommon
