import ThesisCommon.Analysis.GowersMaureyNormingForms

/-! Transposition of the actual tail spreads in the finite coefficient
pairing, and preservation of the source's forms. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem spread_apply (m n : ℕ) (x : C00 𝕜) (i : ℕ) :
    spread m n x i = if n ≤ i then x (i - n + m) else 0 := by
  have h : (Finsupp.lapply i).comp (spread (𝕜 := 𝕜) m n) =
      if n ≤ i then Finsupp.lapply (i - n + m) else 0 := by
    apply Finsupp.lhom_ext
    intro j c
    by_cases hm : m ≤ j
    · by_cases hn : n ≤ i
      · have heq : j - m + n = i ↔ j = i - n + m := by omega
        simp [hm, hn, spread_single, Finsupp.single_apply, heq]
      · have hne : j - m + n ≠ i := by omega
        simp [hm, hn, spread_single, hne]
    · by_cases hn : n ≤ i
      · have hne : j ≠ i - n + m := by omega
        simp [hm, hn, spread_single, hne]
      · simp [hm, hn, spread_single]
  have hh := LinearMap.congr_fun h x
  by_cases hn : n ≤ i <;> simpa [hn] using hh

theorem pairing_spread_left (m n : ℕ) (a x : C00 𝕜) :
    pairing (spread m n a) x = pairing a (spread n m x) := by
  have h : pairing (spread m n a) = (pairing a).comp (spread n m) := by
    apply Finsupp.lhom_ext
    intro i c
    change pairing (spread m n a) (Finsupp.single i c) =
      pairing a (spread n m (Finsupp.single i c))
    rw [pairing_single, spread_apply, spread_single]
    split_ifs <;> simp
  exact LinearMap.congr_fun h x

theorem successive_spread {N : ℕ} {x : Fin N → C00 𝕜} (hx : Successive x)
    (m n : ℕ) : Successive (fun i => spread m n (x i)) := by
  intro i j hij s hs t ht
  have hsn := Finsupp.mem_support_iff.mp hs
  have htn := Finsupp.mem_support_iff.mp ht
  rw [spread_apply] at hsn htn
  have hs' : n ≤ s ∧ x i (s - n + m) ≠ 0 := by
    simpa only [ne_eq, ite_eq_right_iff, Classical.not_imp] using hsn
  have ht' : n ≤ t ∧ x j (t - n + m) ≠ 0 := by
    simpa only [ne_eq, ite_eq_right_iff, Classical.not_imp] using htn
  have hlt := hx i j hij _ (Finsupp.mem_support_iff.mpr hs'.2) _ (Finsupp.mem_support_iff.mpr ht'.2)
  omega

theorem DualUnit.spread {D : ConstructionData 𝕜} {a : C00 𝕜}
    (ha : DualUnit (implicitNorm D) a) (m n : ℕ) :
    DualUnit (implicitNorm D) (GowersMaurey.spread m n a) := by
  intro x
  rw [pairing_spread_left]
  exact (ha _).trans (implicitNorm_spread_le D n m x)

theorem IsForm.spread {D : ConstructionData 𝕜} {k : ℕ} {weight : ℝ}
    (hw : 0 < weight) {a : C00 𝕜} (ha : IsForm D k weight a) (m n : ℕ) :
    IsForm D k weight (GowersMaurey.spread m n a) := by
  obtain ⟨hu, z, hz, hb, heq⟩ := ha
  refine ⟨hu.spread m n, (fun i => GowersMaurey.spread m n (z i)), successive_spread hz m n, ?_, ?_⟩
  · intro i x
    rw [pairing_spread_left]
    exact (hb i _).trans (mul_le_mul_of_nonneg_left (implicitNorm_spread_le D n m x)
      (inv_nonneg.mpr hw.le))
  · rw [heq, map_sum]

end ThesisCommon.GowersMaurey
