import Posets.MrowkaTopology

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter Topology
open scoped ZeroAtInfty
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜] (𝒜 : Set (Set ℕ))

theorem neighborhood_empty_clopen (h𝒜 : IsAlmostDisjoint 𝒜) (A : 𝒜) :
    IsClopen (JFA.mrowkaNeighborhood 𝒜 A ∅) := by
  letI := mrowka_t2 𝒜 h𝒜
  exact ⟨(neighborhood_empty_compact 𝒜 A).isClosed, neighborhood_open 𝒜 A ∅⟩

/-- The actual compact-open neighbourhood characteristic function 1_{U(A)}. -/
def familyVector (h𝒜 : IsAlmostDisjoint 𝒜) (A : 𝒜) : Space 𝕜 𝒜 where
  toFun := (JFA.mrowkaNeighborhood 𝒜 A ∅).indicator (fun _ => 1)
  continuous_toFun := continuous_indicator
    (by simp [neighborhood_empty_clopen 𝒜 h𝒜 A]) continuous_const.continuousOn
  zero_at_infty' := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(neighborhood_empty_compact 𝒜 A).compl_mem_cocompact] with p hp
    exact (Set.indicator_of_notMem hp _).symm

@[simp] theorem familyVector_natural (h𝒜 : IsAlmostDisjoint 𝒜) (A : 𝒜) (n : ℕ) :
    familyVector 𝕜 𝒜 h𝒜 A (Sum.inl n) = indicator 𝕜 A.val n := by
  simp [familyVector, indicator, Set.indicator_apply, JFA.mrowkaNeighborhood, JFA.Mrowka]

@[simp] theorem familyVector_family (h𝒜 : IsAlmostDisjoint 𝒜) (A B : 𝒜) :
    familyVector 𝕜 𝒜 h𝒜 A (Sum.inr B) = if B = A then 1 else 0 := by
  simp [familyVector, Set.indicator_apply, JFA.mrowkaNeighborhood, JFA.Mrowka]

theorem familyVector_isNeighborhoodIndicator (h𝒜 : IsAlmostDisjoint 𝒜) (A : 𝒜) :
    IsNeighborhoodIndicator 𝕜 A (familyVector 𝕜 𝒜 h𝒜 A) :=
  ⟨familyVector_natural 𝕜 𝒜 h𝒜 A, familyVector_family 𝕜 𝒜 h𝒜 A⟩

theorem familyVector_dist_ge_one (h𝒜 : IsAlmostDisjoint 𝒜) {A B : 𝒜} (hAB : A ≠ B) :
    1 ≤ dist (familyVector 𝕜 𝒜 h𝒜 A) (familyVector 𝕜 𝒜 h𝒜 B) := by
  have h := (familyVector 𝕜 𝒜 h𝒜 A - familyVector 𝕜 𝒜 h𝒜 B).toBCF.norm_coe_le_norm (Sum.inr A)
  change ‖familyVector 𝕜 𝒜 h𝒜 A (Sum.inr A) - familyVector 𝕜 𝒜 h𝒜 B (Sum.inr A)‖ ≤ _ at h
  simpa [hAB, dist_eq_norm] using h

/-- The nonseparability needed to pass from Theorem 1.1's uncountable families
to Definition 6.1's FewOperators condition. -/
theorem mrowkaCZero_not_separable (h𝒜 : IsAlmostDisjoint 𝒜) (huncount : ¬ 𝒜.Countable) :
    ¬ TopologicalSpace.SeparableSpace (Space 𝕜 𝒜) := by
  intro hsep
  letI := hsep
  have hd : Pairwise (fun A B : 𝒜 =>
      Disjoint (Metric.ball (familyVector 𝕜 𝒜 h𝒜 A) (1 / 2))
        (Metric.ball (familyVector 𝕜 𝒜 h𝒜 B) (1 / 2))) := by
    intro A B hAB
    apply Metric.ball_disjoint_ball
    linarith [familyVector_dist_ge_one 𝕜 𝒜 h𝒜 hAB]
  letI : Countable 𝒜 := hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun A => ⟨familyVector 𝕜 𝒜 h𝒜 A, Metric.mem_ball_self (by norm_num)⟩)
  exact huncount (Set.to_countable 𝒜)

end Posets
