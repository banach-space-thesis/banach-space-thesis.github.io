import ThesisCommon.Analysis.GowersMaureyHullGap
import ThesisCommon.Analysis.GowersMaureyLargeGap
import ThesisCommon.Analysis.GowersMaureyRapidProducts

/-! Equality of the actual finite-factor hull with f on a gap in the
construction sequence. At the first size the interval extends down to one;
later gaps use the genuine sparse-prefix product estimate. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey.ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜]

theorem interpolationHull_eq_on_gap (D : ConstructionData 𝕜)
    (K : Set ℕ) (hK : K ⊆ D.specialSizes) (n : ℕ) (hnK : D.j n ∉ K)
    {x : ℝ} (hx : 1 ≤ x)
    (hlower : n ≠ 0 → Real.log (Real.log (D.j n : ℝ)) ≤ x)
    (hupper : x ≤ Real.exp (Real.exp (D.j n : ℝ))) :
    submultiplicativeHull (interpolationSeed K) x = logarithmicWeight x := by
  classical
  let r : List ℝ := (Finset.range n).toList.map (fun i => (D.j i : ℝ))
  have hr : r.Nodup := (Finset.nodup_toList _).map (Nat.cast_injective.comp D.j_strict.injective)
  have hr1 : ∀ t ∈ r, 1 ≤ t := by
    intro t ht
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
    exact D.one_le_size i
  have hsmall : r.prod ^ 2 ≤ Real.sqrt x := by
    apply (Real.le_sqrt (sq_nonneg _) (zero_le_one.trans hx)).mpr
    cases n with
    | zero => simpa [r] using hx
    | succ m =>
      have hp : r.prod ≤ (D.j m : ℝ)^2 := by
        simpa only [r, Finset.prod_map_toList] using D.prod_sizes_le_square m
      have hp4 := pow_le_pow_left₀ (zero_le_one.trans (list_prod_ge_one hr1)) hp 4
      have heq : ((D.j m : ℝ)^2)^4 = (D.j m : ℝ)^8 := by ring
      rw [heq] at hp4
      have hl := (D.size_pow_eight_lt_loglog (Nat.lt_succ_self m)).le.trans
        (hlower (Nat.succ_ne_zero m))
      have hpow : (r.prod^2)^2 = r.prod^4 := by ring
      rw [hpow]
      exact hp4.trans hl
  have hK9 : ∀ k ∈ K, 9 ≤ logarithmicWeight k := by
    intro k hk
    have hh := D.specialSize_weight_large (hK hk)
    linarith
  apply interpolationHull_eq_weight_of_sparse_gap K hK9 r hr hr1 hx hsmall
  intro k hk
  obtain ⟨i, hi⟩ := hK hk
  change D.j (2 * i) = k at hi
  by_cases hin : 2 * i < n
  · left
    apply List.mem_map.mpr
    exact ⟨2 * i, by simpa using hin, by simp only [hi]⟩
  · right
    have hni : n < 2 * i := by
      have hne : n ≠ 2 * i := by
        intro he
        apply hnK
        simpa only [he, hi] using hk
      omega
    apply sqrt_weight_ge_of_triple_log_gap
      (by have hh := D.size_large n; linarith)
      (by have hh := D.size_large (2 * i); rw [hi] at hh; linarith)
      ?_ hx hupper
    simpa only [hi] using D.rapid n (2 * i) hni

end ThesisCommon.GowersMaurey.ConstructionData
