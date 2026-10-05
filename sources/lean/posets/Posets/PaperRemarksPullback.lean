import Posets.MainTheorem
import Posets.PosetFamilyEmbedding
import Posets.FamilySupport

/-! The unnumbered proper-pullback example after Corollary 4.10.
In fact no such pullback exists for the strictly nested pair constructed here:
a separable-range pullback would force its uncountable domain family countable.
The printed countable-range implication follows as a weaker consequence. -/

noncomputable section
open Set Filter Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {𝒜 ℬ : Set (Set ℕ)}
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

theorem paper_strict_family_inclusion_is_proper_open_embedding (h : 𝒜 ⊂ ℬ) :
    IsOpenEmbedding (pointInclusion h.subset) ∧
      ¬ Function.Surjective (pointInclusion h.subset) := by
  refine ⟨pointInclusion_isOpenEmbedding h.subset, ?_⟩
  intro hsurj
  apply h.not_subset
  intro B hB
  obtain ⟨p, hp⟩ := hsurj (Sum.inr ⟨B, hB⟩)
  cases p with
  | inl n => cases hp
  | inr A =>
    have heq : A.val = B := congrArg Subtype.val (Sum.inr.inj hp)
    exact heq ▸ A.property

theorem paper_mrowka_exists_function_one (hℬ : IsAlmostDisjoint ℬ) (p : Mrowka ℬ) :
    ∃ f : Space 𝕜 ℬ, f p = 1 := by
  cases p with
  | inl n => exact ⟨isolatedVector 𝕜 ℬ n, by simp⟩
  | inr B => exact ⟨familyVector 𝕜 ℬ hℬ B, by simp⟩

def paperMrowkaPullback (θ : Mrowka 𝒜 → Mrowka ℬ) (hθ : Continuous θ)
    (hvanish : ∀ f : Space 𝕜 ℬ, Tendsto (fun x => f (θ x))
      (cocompact (Mrowka 𝒜)) (𝓝 0)) : Space 𝕜 ℬ →L[𝕜] Space 𝕜 𝒜 :=
  ({ toFun := fun f =>
       { toFun := fun x => f (θ x)
         continuous_toFun := f.continuous.comp hθ
         zero_at_infty' := hvanish f }
     map_add' := by intro f g; ext x; rfl
     map_smul' := by intro a f; ext x; rfl } :
    Space 𝕜 ℬ →ₗ[𝕜] Space 𝕜 𝒜).mkContinuous 1 (by
      intro f
      simp only [one_mul]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
      intro x
      exact f.toBCF.norm_coe_le_norm (θ x))

theorem paper_countable_family_of_separable_pullback (hℬ : IsAlmostDisjoint ℬ)
    (θ : Mrowka 𝒜 → Mrowka ℬ) (T : Space 𝕜 ℬ →L[𝕜] Space 𝕜 𝒜)
    (hT : HasSeparableRange 𝕜 (Space 𝕜 ℬ) (Space 𝕜 𝒜) T)
    (happly : ∀ f x, T f x = f (θ x)) : 𝒜.Countable := by
  letI : TopologicalSpace.SeparableSpace (Set.range T) := hT.separableSpace
  have hc := familySupportSet_countable_of_separable (𝕜 := 𝕜) (Set.range T)
  have hfull : (univ : Set 𝒜) ⊆ familySupportSet 𝕜 (Set.range T) := by
    intro A _
    obtain ⟨f, hf⟩ := paper_mrowka_exists_function_one (𝕜 := 𝕜) hℬ (θ (.inr A))
    exact ⟨T f, ⟨f, rfl⟩, by rw [happly, hf]; exact one_ne_zero⟩
  letI : Countable 𝒜 := Set.countable_univ_iff.mp (hc.mono hfull)
  exact Set.to_countable 𝒜

/-- A strict nested pair, retaining the actual off-order separable-range conclusion. -/
theorem paper_exists_strict_nested_families (𝕜 : Type) [RCLike 𝕜] :
    ∃ 𝒜 ℬ : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧ IsAlmostDisjoint ℬ ∧
      ¬ 𝒜.Countable ∧ 𝒜 ⊂ ℬ ∧
      ∀ T : Space 𝕜 ℬ →L[𝕜] Space 𝕜 𝒜,
        HasSeparableRange 𝕜 (Space 𝕜 ℬ) (Space 𝕜 𝒜) T := by
  let e := countablePosetSetEmbedding (Fin 2)
  obtain ⟨F, B, H, C, hm, hd, hi, hs, hH, hC, hinj, hprivate, hr⟩ :=
    exists_main_rejection_witnesses (fun M => lemma_5_2_proof (𝕜 := 𝕜) closedTreeFamily M)
  let 𝒟 := orderedPartitionFamily e H C
  have hD (t : Fin 2) : 𝒟 t ⊆ Set.range B :=
    partitionFamily_subset hH hC (commonCoordinateEmbedding e t)
  have hglobal := witnessFamily_almostDisjoint closedTreeFamily_almostDisjoint F hm hd B hi hs
  have had (t : Fin 2) : IsAlmostDisjoint (𝒟 t) := almostDisjoint_of_subset hglobal (hD t)
  have huncount (t : Fin 2) : ¬ (𝒟 t).Countable :=
    uncountable_of_card_continuum (orderedPartitionFamily_card e H hinj t)
  have hsub : 𝒟 0 ⊆ 𝒟 1 := orderedPartitionFamily_mono e H C (by decide)
  have hdiff : ¬ (𝒟 1 \ 𝒟 0).Countable :=
    uncountable_of_card_continuum (orderedPartitionFamily_diff_card e hinj hprivate
      (show ¬ (1 : Fin 2) ≤ 0 by decide))
  have hstrict : 𝒟 0 ⊂ 𝒟 1 := Set.ssubset_iff_subset_ne.mpr ⟨hsub, by
    intro heq
    apply hdiff
    simp [heq]⟩
  have hreject (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M)
      (hbad : ¬ ScalarShiftAcceptedOffCountable closedTreeFamily M) :
      ¬ {A ∈ 𝒟 1 ∩ 𝒟 0 | Rejects 𝕜 A A M}.Countable := by
    intro hcount
    apply hr M hM hbad
    apply hcount.mono
    intro A h
    exact ⟨⟨Or.inl h.1, Or.inl h.1⟩, h.2⟩
  refine ⟨𝒟 0, 𝒟 1, had 0, had 1, huncount 0, hstrict, ?_⟩
  intro T
  obtain ⟨a, E, hE, hself, hcross⟩ := main_operator_admission_of_witnesses
    closedTreeFamily_almostDisjoint F hm hd B hi hs (hD 1) (hD 0) hreject T
  exact (offOrder_factorization_of_admission (had 1) (had 0)
    (almostDisjoint_of_subset hglobal (Set.union_subset (hD 1) (hD 0))) hdiff
      T a E E hE hE hself hcross).hasSeparableRange

/-- The Section 4 example, in the stronger form excluding any such composition map. -/
theorem paper_exists_nested_no_czero_pullback (𝕜 : Type) [RCLike 𝕜] :
    ∃ 𝒜 ℬ : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧ IsAlmostDisjoint ℬ ∧
      ¬ 𝒜.Countable ∧ 𝒜 ⊂ ℬ ∧
      ∀ θ : Mrowka 𝒜 → Mrowka ℬ, Continuous θ →
        ¬ (∀ f : Space 𝕜 ℬ, Tendsto (fun x => f (θ x))
          (cocompact (Mrowka 𝒜)) (𝓝 0)) := by
  obtain ⟨𝒜, ℬ, h𝒜, hℬ, huncount, hstrict, hsep⟩ := paper_exists_strict_nested_families 𝕜
  refine ⟨𝒜, ℬ, h𝒜, hℬ, huncount, hstrict, ?_⟩
  intro θ hθ hvanish
  let T := paperMrowkaPullback (𝕜 := 𝕜) θ hθ hvanish
  exact huncount (paper_countable_family_of_separable_pullback hℬ θ T (hsep T)
    (fun _ _ => rfl))

/-- The literal countable-range conclusion printed after Corollary 4.10. -/
theorem paper_exists_nested_countable_range_pullback (𝕜 : Type) [RCLike 𝕜] :
    ∃ 𝒜 ℬ : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧ IsAlmostDisjoint ℬ ∧
      ¬ 𝒜.Countable ∧ 𝒜 ⊂ ℬ ∧
      ∀ θ : Mrowka 𝒜 → Mrowka ℬ, Continuous θ →
        (∀ f : Space 𝕜 ℬ, Tendsto (fun x => f (θ x))
          (cocompact (Mrowka 𝒜)) (𝓝 0)) → (Set.range θ).Countable := by
  obtain ⟨𝒜, ℬ, h𝒜, hℬ, huncount, hstrict, hno⟩ := paper_exists_nested_no_czero_pullback 𝕜
  exact ⟨𝒜, ℬ, h𝒜, hℬ, huncount, hstrict, fun θ hθ hv => (hno θ hθ hv).elim⟩

end Posets
