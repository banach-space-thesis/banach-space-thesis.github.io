import ThesisCommon.Analysis.GowersMaureyFinitePacking
import ThesisCommon.Analysis.FiniteIntervalDomination

/-! Source Section 2, Lemma 2, for the actual constructed norm. The explicit
nonzero condition is necessary: the zero vector has empty support range,
which cannot carry a probability. An all-vector disjunction is also given. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_interval_probability_of_intervalNorm_le (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 0 < N) {x : C00 𝕜} (hx0 : x ≠ 0) (hx : intervalNorm D N x ≤ 1) :
    ∃ μ : ℕ → ℝ, (∀ n, 0 ≤ μ n) ∧
      (∀ n, n ∉ (supportInterval x).set → μ n = 0) ∧
      (∑ n ∈ (supportInterval x).set, μ n) = 1 ∧
      ∀ E : Interval, E.set ⊆ (supportInterval x).set →
        (N : ℝ)⁻¹ < implicitNorm D (restrict E x) →
        implicitNorm D (restrict E x) ≤ ∑ n ∈ E.set, μ n := by
  classical
  have hs : x.support.Nonempty := Finsupp.support_nonempty_iff.mpr hx0
  have hLR : (supportInterval x).first ≤ (supportInterval x).last := by
    simp only [supportInterval, dif_pos hs]
    exact Finset.min'_le _ _ (Finset.max'_mem _ hs)
  let w (a b : ℕ) := largeIntervalWeight D N x ⟨a, b⟩
  have hpack : ∀ S, FiniteIntervalDomination.IsPacking ((supportInterval x).last + 1) S →
      (∀ E ∈ S, (supportInterval x).first ≤ E.1) → (∑ E ∈ S, w E.1 E.2) ≤ 1 := by
    intro S hS _
    exact largeIntervalWeight_finset_packing D hN hx S (fun E hE => (hS.1 E hE).1) hS.2
  obtain ⟨μ, hpos, hsupp, htotal, hdom⟩ :=
    FiniteIntervalDomination.exists_probability_on_Icc_dominating_intervals w hLR hpack
  refine ⟨μ, hpos, hsupp, htotal, ?_⟩
  intro E hsub hlarge
  have hne : E.set.Nonempty := by
    by_contra he
    have he' : E.set = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have hz : restrict E x = 0 := by ext n; simp [he']
    rw [hz, map_zero] at hlarge
    exact (not_lt_of_ge (inv_nonneg.mpr (Nat.cast_nonneg N))) hlarge
  have hab : E.first ≤ E.last := Finset.nonempty_Icc.mp hne
  have ha : (supportInterval x).first ≤ E.first :=
    (Finset.mem_Icc.mp (hsub (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩))).1
  have hb : E.last ≤ (supportInterval x).last :=
    (Finset.mem_Icc.mp (hsub (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩))).2
  have hd := hdom E.first E.last ha hab hb
  simpa only [w, largeIntervalWeight, if_pos hlarge] using hd

theorem eq_zero_or_exists_interval_probability (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 0 < N) {x : C00 𝕜} (hx : intervalNorm D N x ≤ 1) :
    x = 0 ∨ ∃ μ : ℕ → ℝ, (∀ n, 0 ≤ μ n) ∧
      (∀ n, n ∉ (supportInterval x).set → μ n = 0) ∧
      (∑ n ∈ (supportInterval x).set, μ n) = 1 ∧
      ∀ E : Interval, E.set ⊆ (supportInterval x).set →
        (N : ℝ)⁻¹ < implicitNorm D (restrict E x) →
        implicitNorm D (restrict E x) ≤ ∑ n ∈ E.set, μ n := by
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · exact Or.inr (exists_interval_probability_of_intervalNorm_le D hN hx0 hx)

end ThesisCommon.GowersMaurey
