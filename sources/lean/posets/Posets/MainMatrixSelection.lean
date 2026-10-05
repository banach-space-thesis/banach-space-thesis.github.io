import Posets.MainOperatorReduction

/-! The common rejecting family excludes bad reduced matrices in Section 5. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 ℬ 𝒞 : Set (Set ℕ)}

/-- Countably many source members can self-reject a reduced matrix when they
also occur in the target family. -/
theorem reducedMatrix_selfRejecting_countable (h𝒜 : IsAlmostDisjoint 𝒜)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) :
    {B ∈ 𝒜 ∩ ℬ | Rejects 𝕜 B B (reducedMatrix 𝕜 T)}.Countable := by
  apply ((operatorExceptionalFamily_countable h𝒜 T).image Subtype.val).mono
  rintro B ⟨⟨hBA, hBB⟩, hr⟩
  have he : (⟨B, hBA⟩ : 𝒜) ∈ operatorExceptionalFamily h𝒜 T := by
    by_contra hn
    exact hr ⟨_, operator_family_matrix_tendsto h𝒜 T ⟨B, hBA⟩ hn ⟨B, hBB⟩⟩
  exact ⟨⟨B, hBA⟩, he, rfl⟩

/-- Being good in step 2 means acceptance after a scalar shift and removal of
a countable source subfamily. The exclusion need not be contained in the source;
intersecting it with the source makes this definition identical to the printed one. -/
def ScalarShiftAcceptedOffCountable (𝒜 : Set (Set ℕ)) (M : ScalarMatrix 𝕜) : Prop :=
  ∃ C : Set (Set ℕ), C.Countable ∧ ∃ a : 𝕜,
    Accepts 𝕜 (𝒜 \ C) (𝒜 \ C) (M - a • identityMatrix 𝕜)

theorem scalarShiftAcceptedOffCountable_iff_subfamily (M : ScalarMatrix 𝕜) :
    ScalarShiftAcceptedOffCountable 𝒞 M ↔
      ∃ C : Set (Set ℕ), C ⊆ 𝒞 ∧ C.Countable ∧ ∃ a : 𝕜,
        Accepts 𝕜 (𝒞 \ C) (𝒞 \ C) (M - a • identityMatrix 𝕜) := by
  constructor
  · rintro ⟨C, hC, a, ha⟩
    refine ⟨𝒞 ∩ C, Set.inter_subset_left, hC.mono Set.inter_subset_right, a, ?_⟩
    have he : 𝒞 \ (𝒞 ∩ C) = 𝒞 \ C := by
      ext A
      simp only [Set.mem_diff, Set.mem_inter_iff]
      tauto
    rwa [he]
  · rintro ⟨C, _, hC, a, ha⟩
    exact ⟨C, hC, a, ha⟩

/-- The uncountably many common rejection witnesses supplied by the construction
force every operator's reduced matrix into the good alternative. -/
theorem reducedMatrix_scalarShiftAcceptedOffCountable (h𝒜 : IsAlmostDisjoint 𝒜)
    (hreject : ∀ M : ScalarMatrix 𝕜, HasBoundedRows 𝕜 M →
      ¬ ScalarShiftAcceptedOffCountable 𝒞 M →
      ¬ {B ∈ 𝒜 ∩ ℬ | Rejects 𝕜 B B M}.Countable)
    (T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ) :
    ScalarShiftAcceptedOffCountable 𝒞 (reducedMatrix 𝕜 T) := by
  by_contra hbad
  exact hreject _ ⟨reducedMatrix_row_summable T, ‖T‖, reducedMatrix_row_bound T⟩ hbad
    (reducedMatrix_selfRejecting_countable h𝒜 T)

end Posets
