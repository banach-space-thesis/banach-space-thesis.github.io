import Posets.IdealCountTransfer

/-! Maximal closed ideals transfer through a nonzero quotient realization.
Every maximal ideal contains the separable-range kernel. -/

noncomputable section
open Set ThesisCommon
namespace Posets

section General
variable {𝕜 A B : Type*} [RCLike 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A] [CompleteSpace A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] [Mul B] [CompleteSpace B]
    (θ : BoundedHom 𝕜 A B) (hsurj : Function.Surjective θ)

include hsurj in
theorem closedIdeal_preimage_maximal_iff {J : Set B} (hJ : IsClosedIdeal 𝕜 J) :
    IsMaximalClosedIdeal 𝕜 (θ ⁻¹' J) ↔ IsMaximalClosedIdeal 𝕜 J := by
  constructor
  · intro h
    refine ⟨hJ, fun he => h.2.1 (by simp [he]), ?_⟩
    intro K hK hJK
    rcases h.2.2 (θ ⁻¹' K) (closedIdeal_preimage θ hK)
      (Set.preimage_mono hJK) with he | he
    · left
      have hm := congrArg (fun S => θ '' S) he
      simpa only [Set.image_preimage_eq _ hsurj] using hm
    · right
      have hm := congrArg (fun S => θ '' S) he
      simpa only [Set.image_preimage_eq _ hsurj, Set.image_univ,
        Set.range_eq_univ.mpr hsurj] using hm
  · intro h
    refine ⟨closedIdeal_preimage θ hJ, ?_, ?_⟩
    · intro he
      apply h.2.1
      have hm := congrArg (fun S => θ '' S) he
      simpa only [Set.image_preimage_eq _ hsurj, Set.image_univ,
        Set.range_eq_univ.mpr hsurj] using hm
    · intro I hI hJI
      have hk := (closedIdeal_kernel_subset_preimage θ hJ).trans hJI
      have hi : J ⊆ θ '' I := by
        intro b hb
        obtain ⟨a, rfl⟩ := hsurj b
        exact ⟨a, hJI hb, rfl⟩
      rcases h.2.2 (θ '' I) (closedIdeal_image θ hsurj hI hk) hi with he | he
      · left
        have hm := congrArg (fun S => θ ⁻¹' S) he
        simpa only [closedIdeal_preimage_image θ hI hk] using hm
      · right
        have hm := congrArg (fun S => θ ⁻¹' S) he
        simpa only [closedIdeal_preimage_image θ hI hk, Set.preimage_univ] using hm

end General

section Mrowka
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}
    {C : Type} [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
    [CompleteSpace C] [Nontrivial C]
    (θ : BoundedHom 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) C)
    (ρ : BoundedHom 𝕜 C (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜))
    (hs : StrongSplit 𝕜 (Space 𝕜 𝒜) C θ ρ)

include hs in
theorem maximalClosedIdeal_contains_separable (h𝒜 : IsAlmostDisjoint 𝒜)
    {I : Set (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜)} (hI : IsMaximalClosedIdeal 𝕜 I) :
    {T | HasSeparableRange 𝕜 (Space 𝕜 𝒜) (Space 𝕜 𝒜) T} ⊆ I := by
  let K : Set (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) := {T | IsCompactOperator T}
  let S : Set (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) := {T | HasSeparableRange 𝕜 _ _ T}
  have hK : IsClosedIdeal 𝕜 K := JFA.compactOperators_closedIdeal
  have hS : IsClosedIdeal 𝕜 S := JFA.separableOperators_closedIdeal
  have hSproper : S ≠ Set.univ := by
    intro he
    obtain ⟨c, hc⟩ := exists_ne (0 : C)
    obtain ⟨T, hT⟩ := hs.1 c
    apply hc
    rw [← hT]
    apply (hs.2.1 T).mpr
    change T ∈ S
    rw [he]
    exact Set.mem_univ T
  have hI0 : I ≠ {0} := by
    intro he
    have hz : I ⊆ K := by
      rw [he]
      intro T hT
      rcases Set.mem_singleton_iff.mp hT with rfl
      exact isCompactOperator_zero
    rcases hI.2.2 K hK hz with hk | hk
    · exact mrowka_compactOperators_ne_zero (𝕜 := 𝕜) (𝒜 := 𝒜) (hk.trans he)
    · exact mrowka_compactOperators_ne_univ h𝒜 hk
  apply mrowka_separable_subset_ideal_of_noncompact h𝒜 hI.1
  intro hik
  have hki : K ⊆ I := mrowka_compactOperators_minimal h𝒜 hI.1 hI0
  have hks : K ⊆ S := fun T hT => JFA.hasSeparableRange_of_isCompactOperator T hT
  rcases hI.2.2 S hS (hik.trans hks) with he | he
  · obtain ⟨P, hPs, hPc⟩ := mrowka_exists_separable_noncompact (𝕜 := 𝕜) h𝒜
    exact hPc (hik (he ▸ hPs))
  · exact hSproper he

/-- Exact bijection of maximal ideals for every nonzero product realization. -/
def strongSplitMaximalIdealEquiv (h𝒜 : IsAlmostDisjoint 𝒜) :
    MaximalClosedIdeals 𝕜 C ≃
      MaximalClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) where
  toFun J := ⟨θ ⁻¹' J.val,
    (closedIdeal_preimage_maximal_iff θ hs.1 J.property.1).mpr J.property⟩
  invFun I := by
    have hk : {T | θ T = 0} ⊆ I.val := fun T hT =>
      maximalClosedIdeal_contains_separable θ ρ hs h𝒜 I.property ((hs.2.1 T).mp hT)
    have hi := closedIdeal_image θ hs.1 I.property.1 hk
    refine ⟨θ '' I.val, (closedIdeal_preimage_maximal_iff θ hs.1 hi).mp ?_⟩
    rw [closedIdeal_preimage_image θ I.property.1 hk]
    exact I.property
  left_inv J := Subtype.ext (Set.image_preimage_eq _ hs.1)
  right_inv I := by
    apply Subtype.ext
    exact closedIdeal_preimage_image θ I.property.1 (fun T hT =>
      maximalClosedIdeal_contains_separable θ ρ hs h𝒜 I.property ((hs.2.1 T).mp hT))

end Mrowka
end Posets
