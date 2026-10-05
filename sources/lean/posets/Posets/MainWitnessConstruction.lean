import Posets.MainCardinality
import Posets.MainWitnessFamilies

/-! The transfinite construction, with a common continuum of witnesses for
each requirement and a disjoint continuum of private coordinate witnesses. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
open Cardinal

structure FiniteWitnessPool (𝒞 : Set (Set ℕ)) where
  cover : Set ℕ → Finset (Set ℕ)
  member : ∀ i A, A ∈ cover i → A ∈ 𝒞
  witness : Set ℕ → Set ℕ
  infinite : ∀ i, (witness i).Infinite
  subset : ∀ i, witness i ⊆ ⋃ A ∈ cover i, A
  disjoint : Pairwise fun i j => Disjoint (cover i) (cover j)

theorem uncountable_of_setNat_fiber {α : Type} {W : Set α}
    (f : Set ℕ → α) (hf : Function.Injective f) (hW : ∀ β, f β ∈ W) :
    ¬ W.Countable := by
  intro hcount
  have hle := Cardinal.mk_le_of_injective (f := fun β => (⟨f β, hW β⟩ : W))
    (fun β γ h => hf (congrArg Subtype.val h))
  rw [Cardinal.mk_set_nat] at hle
  exact Cardinal.aleph0_lt_continuum.not_ge (hle.trans hcount.le_aleph0)

/-- The requirements may be arbitrary predicates on the selected witnesses.
`none` labels private witnesses; `some s` labels the common witnesses for `s`. -/
theorem exists_common_private_witnesses {σ : Type} (hσ : #σ ≤ 𝔠)
    {𝒞 : Set (Set ℕ)} (h𝒞 : IsAlmostDisjoint 𝒞)
    (pool : Option σ → FiniteWitnessPool 𝒞) (R : σ → Set ℕ → Prop)
    (hR : ∀ s i, R s ((pool (some s)).witness i)) :
    ∃ F : ContinuumStage → Finset (Set ℕ),
    ∃ B : ContinuumStage → Set ℕ,
    ∃ H : Set (Set ℕ), ∃ C : Set ℕ × Set ℕ → Set ℕ,
      (∀ i A, A ∈ F i → A ∈ 𝒞) ∧
      (Pairwise fun i j => Disjoint (F i) (F j)) ∧
      (∀ i, (B i).Infinite) ∧ (∀ i, B i ⊆ ⋃ A ∈ F i, A) ∧
      H ⊆ Set.range B ∧ Set.range C ⊆ Set.range B ∧
      Function.Injective C ∧ (∀ α β, C (α, β) ∉ H) ∧
      (∀ s, ¬ {A ∈ H | R s A}.Countable) := by
  let e := continuumStageEquiv hσ
  let F₀ : ContinuumStage → Set ℕ → Finset (Set ℕ) := fun i => (pool (e i).1).cover
  have hd₀ (i) : Pairwise fun j k => Disjoint (F₀ i j) (F₀ i k) := (pool (e i).1).disjoint
  let g := transfiniteFiniteWitnessChoice F₀ hd₀
  let F : ContinuumStage → Finset (Set ℕ) := fun i => F₀ i (g i)
  let B : ContinuumStage → Set ℕ := fun i => (pool (e i).1).witness (g i)
  have hm (i A) (h : A ∈ F i) : A ∈ 𝒞 := (pool (e i).1).member (g i) A h
  have hd : Pairwise fun i j => Disjoint (F i) (F j) :=
    transfiniteFiniteWitnessChoice_disjoint F₀ hd₀
  have hi (i) : (B i).Infinite := (pool (e i).1).infinite (g i)
  have hs (i) : B i ⊆ ⋃ A ∈ F i, A := (pool (e i).1).subset (g i)
  have hBinj := witnessFamily_injective h𝒞 F hm hd B hi hs
  let H : Set (Set ℕ) := {A | ∃ s β, B (e.symm (some s, β)) = A}
  let C : Set ℕ × Set ℕ → Set ℕ := fun p => B (e.symm (none, setNatPairEquiv p))
  refine ⟨F, B, H, C, hm, hd, hi, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rintro A ⟨s, β, rfl⟩
    exact ⟨_, rfl⟩
  · rintro A ⟨p, rfl⟩
    exact ⟨_, rfl⟩
  · intro p q h
    exact setNatPairEquiv.injective (congrArg Prod.snd (e.symm.injective (hBinj h)))
  · rintro α β ⟨s, γ, h⟩
    have he : (some s, γ) = (none, setNatPairEquiv (α, β)) :=
      e.symm.injective (hBinj h)
    exact Option.noConfusion (congrArg Prod.fst he)
  · intro s
    apply uncountable_of_setNat_fiber (fun β => B (e.symm (some s, β)))
    · intro β γ h
      exact congrArg Prod.snd (e.symm.injective (hBinj h))
    · intro β
      refine ⟨⟨s, β, rfl⟩, ?_⟩
      change R s ((pool (e (e.symm (some s, β))).1).witness (g (e.symm (some s, β))))
      rw [e.apply_symm_apply]
      exact hR s _

end Posets
