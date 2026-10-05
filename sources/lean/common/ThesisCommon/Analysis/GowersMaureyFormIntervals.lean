import ThesisCommon.Analysis.GowersMaureyNormingForms

/-! Interval decompositions of genuine forms and their elementary finite
mass identities, including empty pieces and a piece equal to the whole
interval. The latter case is needed in the minimal-interval argument. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem FiniteIntervalFamily.disjoint {k : ℕ} (I : FiniteIntervalFamily k)
    {i j : Fin k} (hij : i ≠ j) : Disjoint (I.interval i).set (I.interval j).set := by
  apply Finset.disjoint_left.mpr
  intro n hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (lt_irrefl n) (I.successive i j h n hi n hj)
  · exact (lt_irrefl n) (I.successive j i h n hj n hi)

def FiniteIntervalFamily.inter {k : ℕ} (I : FiniteIntervalFamily k) (E : Interval) :
    FiniteIntervalFamily k where
  interval i := (I.interval i).inter E
  successive i j hij s hs t ht := I.successive i j hij s
    ((Interval.mem_inter _ _ _).mp hs).1 t ((Interval.mem_inter _ _ _).mp ht).1

theorem FiniteIntervalFamily.inter_subset {k : ℕ} (I : FiniteIntervalFamily k) (E : Interval)
    (i : Fin k) : ((I.inter E).interval i).set ⊆ E.set := by
  intro n hn
  exact ((Interval.mem_inter _ _ _).mp hn).2

theorem restrict_eq_zero_of_empty {E : Interval} (hE : E.set = ∅) (x : C00 𝕜) :
    restrict E x = 0 := by ext n; simp [hE]

theorem restrict_eq_of_set_eq {E F : Interval} (h : E.set = F.set) (x : C00 𝕜) :
    restrict E x = restrict F x := by ext n; simp [h]

theorem FiniteIntervalFamily.intervalSum_eq_of_full {k : ℕ} (I : FiniteIntervalFamily k)
    {E : Interval} (hsub : ∀ i, (I.interval i).set ⊆ E.set)
    {i : Fin k} (hi : (I.interval i).set = E.set) (D : ConstructionData 𝕜) (x : C00 𝕜) :
    intervalSum D I x = implicitNorm D (restrict E x) := by
  rw [intervalSum_apply, Finset.sum_eq_single i]
  · rw [restrict_eq_of_set_eq hi]
  · intro j _ hji
    have hzero : (I.interval j).set = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hni : n ∈ (I.interval i).set := by rw [hi]; exact hsub j hn
      exact Finset.disjoint_left.mp (I.disjoint hji) hn hni
    rw [restrict_eq_zero_of_empty hzero, map_zero]
  · simp

theorem FiniteIntervalFamily.sum_mass_le {k : ℕ} (I : FiniteIntervalFamily k)
    {E : Interval} (hsub : ∀ i, (I.interval i).set ⊆ E.set)
    (μ : ℕ → ℝ) (hμ : ∀ n, 0 ≤ μ n) :
    (∑ i, ∑ n ∈ (I.interval i).set, μ n) ≤ ∑ n ∈ E.set, μ n := by
  classical
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin k)), ∀ j ∈ Finset.univ, i ≠ j →
      Disjoint (I.interval i).set (I.interval j).set := by
    intro i _ j _ hij
    exact I.disjoint hij
  rw [← Finset.sum_biUnion hd]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hn
    exact hsub i hi
  · intro n _ _
    exact hμ n

theorem IsForm.exists_interval_decomposition {D : ConstructionData 𝕜} {k : ℕ}
    {weight : ℝ} {a : C00 𝕜} (ha : IsForm D k weight a)
    (E : Interval) (x : C00 𝕜) :
    ∃ I : FiniteIntervalFamily k, (∀ i, (I.interval i).set ⊆ E.set) ∧
      ‖pairing a (GowersMaurey.restrict E x)‖ ≤ weight⁻¹ * intervalSum D I x := by
  obtain ⟨_, z, hz, hb, rfl⟩ := ha
  let I := (supportIntervalFamily z hz).inter E
  refine ⟨I, fun i => FiniteIntervalFamily.inter_subset _ _ i, ?_⟩
  rw [pairing_sum_left, intervalSum_apply, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have heq : pairing (z i) (GowersMaurey.restrict E x) =
      pairing (z i) (GowersMaurey.restrict (I.interval i) x) := by
    rw [← pairing_restrict_supportInterval (z i) (GowersMaurey.restrict E x), restrict_restrict]
    rfl
  rw [heq]
  exact hb i _

end ThesisCommon.GowersMaurey
