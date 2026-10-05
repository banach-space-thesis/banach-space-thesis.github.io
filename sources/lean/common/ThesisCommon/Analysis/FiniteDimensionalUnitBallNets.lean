import ThesisCommon.Analysis.FiniteDimensionalNets

/-! A maximal finite separated subset supplies an actual finite unit-ball
net with cardinality bounded only by the dimension and the requested radius. -/
noncomputable section
open Module
namespace ThesisCommon

section Real
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_real_unitBall_net_card_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset E, (∀ y ∈ s, ‖y‖ ≤ 1) ∧
      s.card ≤ ⌈(1 + 2 / δ) ^ finrank ℝ E⌉₊ ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, ‖x - y‖ ≤ δ := by
  classical
  let Good (s : Finset E) : Prop :=
    (∀ c ∈ s, ‖c‖ ≤ 1) ∧ ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖
  let cards : Set ℕ := {n | ∃ s : Finset E, s.card = n ∧ Good s}
  have hcard (s : Finset E) (hs : Good s) : s.card ≤ ⌈(1 + 2 / δ) ^ finrank ℝ E⌉₊ := by
    exact_mod_cast (unitBall_separated_card_le s hδ hs.1 hs.2).trans (Nat.le_ceil _)
  have hbdd : BddAbove cards := by
    refine ⟨⌈(1 + 2 / δ) ^ finrank ℝ E⌉₊, ?_⟩
    rintro n ⟨s, rfl, hs⟩
    exact hcard s hs
  have hne : cards.Nonempty := by
    refine ⟨0, ∅, rfl, ?_⟩
    simp [Good]
  obtain ⟨n, hn, hmax⟩ := hbdd.exists_isGreatest_of_nonempty hne
  obtain ⟨s, hsn, hs⟩ := hn
  subst n
  refine ⟨s, hs.1, hcard s hs, ?_⟩
  intro x hx
  by_contra! hfar
  have hnot : x ∉ s := by
    intro hmem
    have h := hfar x hmem
    simpa using hδ.le.not_gt (by simpa using h)
  have hgood : Good (insert x s) := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hs.1 y hy
    · intro c hc d hd hcd
      rcases Finset.mem_insert.mp hc with hcx | hcs
      · subst c
        rcases Finset.mem_insert.mp hd with hdx | hds
        · exact (hcd hdx.symm).elim
        · exact (hfar d hds).le
      · rcases Finset.mem_insert.mp hd with hdx | hds
        · subst d
          rw [norm_sub_rev]
          exact (hfar c hcs).le
        · exact hs.2 c hcs d hds hcd
  have hle : (insert x s).card ≤ s.card := hmax ⟨insert x s, rfl, hgood⟩
  rw [Finset.card_insert_of_notMem hnot] at hle
  omega

end Real

/-- A common real/complex bound; real spaces also satisfy the sharper
exponent `d` in `exists_real_unitBall_net_card_le`. -/
def finiteDimensionalNetBound (d : ℕ) (δ : ℝ) : ℕ :=
  ⌈(1 + 2 / δ) ^ (2 * d)⌉₊

theorem one_le_finiteDimensionalNetBound (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    1 ≤ finiteDimensionalNetBound d δ := by
  apply Nat.one_le_ceil_iff.mpr
  exact pow_pos (by positivity) _

theorem finiteDimensionalNetBound_mono_dim {d e : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hde : d ≤ e) :
    finiteDimensionalNetBound d δ ≤ finiteDimensionalNetBound e δ := by
  apply Nat.ceil_le_ceil
  have hbase : 1 ≤ 1 + 2 / δ := le_add_of_nonneg_right (by positivity)
  exact pow_le_pow_right₀ hbase (Nat.mul_le_mul_left 2 hde)

theorem exists_unitBall_net_card_le (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset E, (∀ y ∈ s, ‖y‖ ≤ 1) ∧
      s.card ≤ finiteDimensionalNetBound (finrank 𝕜 E) δ ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, ‖x - y‖ ≤ δ := by
  letI : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  letI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ 𝕜 E
  obtain ⟨s, hs, hcard, hcover⟩ := exists_real_unitBall_net_card_le (E := E) hδ
  refine ⟨s, hs, hcard.trans ?_, hcover⟩
  apply Nat.ceil_le_ceil
  have hdim : finrank ℝ E ≤ 2 * finrank 𝕜 E := by
    rw [← Module.finrank_mul_finrank ℝ 𝕜 E]
    exact Nat.mul_le_mul_right _ (RCLike.finrank_le_two 𝕜)
  have hbase : 1 ≤ 1 + 2 / δ := le_add_of_nonneg_right (by positivity)
  exact pow_le_pow_right₀ hbase hdim

theorem exists_unitBall_net_card_le_of_finrank_le (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {d : ℕ} (hd : finrank 𝕜 E ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset E, (∀ y ∈ s, ‖y‖ ≤ 1) ∧
      s.card ≤ finiteDimensionalNetBound d δ ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, ‖x - y‖ ≤ δ := by
  obtain ⟨s, hs, hcard, hcover⟩ := exists_unitBall_net_card_le 𝕜 E hδ
  exact ⟨s, hs, hcard.trans (finiteDimensionalNetBound_mono_dim hδ hd), hcover⟩

end ThesisCommon
