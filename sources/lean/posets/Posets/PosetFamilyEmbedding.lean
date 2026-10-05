import Posets.QuotientStatements
import Mathlib.Data.Sigma.Order
import Mathlib.Order.Hom.WithTopBot

/-! Countable disjoint unions of component posets, with shared added
endpoints, provide the global family used for product quotient realizations. -/

noncomputable section
namespace Posets

def sigmaFiberEmbedding {I : Type*} (P : I → Type*) [∀ i, PartialOrder (P i)]
    (i : I) : P i ↪o (Σ i, P i) where
  toFun := Sigma.mk i
  inj' := fun a b h => by simpa using h
  map_rel_iff' := Sigma.mk_le_mk_iff

def boundedFiberEmbedding {I : Type*} (P : I → Type*) [∀ i, PartialOrder (P i)]
    (i : I) : BoundedExtension (P i) ↪o BoundedExtension (Σ i, P i) :=
  (sigmaFiberEmbedding P i).withTopMap.withBotMap

@[simp] theorem boundedFiberEmbedding_bot {I : Type*} (P : I → Type*)
    [∀ i, PartialOrder (P i)] (i : I) : boundedFiberEmbedding P i ⊥ = ⊥ := rfl

@[simp] theorem boundedFiberEmbedding_top {I : Type*} (P : I → Type*)
    [∀ i, PartialOrder (P i)] (i : I) : boundedFiberEmbedding P i ⊤ = ⊤ := rfl

@[simp] theorem boundedFiberEmbedding_middle {I : Type*} (P : I → Type*)
    [∀ i, PartialOrder (P i)] (i : I) (p : P i) :
    boundedFiberEmbedding P i (middle p) = middle (⟨i, p⟩ : Σ i, P i) := rfl

theorem sigma_not_le_of_ne {I : Type*} {P : I → Type*} [∀ i, PartialOrder (P i)]
    {i j : I} (h : i ≠ j) (p : P i) (q : P j) :
    ¬ (⟨i, p⟩ : Σ i, P i) ≤ ⟨j, q⟩ := fun hpq => h (Sigma.le_def.mp hpq).1

theorem middle_sigma_not_le_of_ne {I : Type*} {P : I → Type*} [∀ i, PartialOrder (P i)]
    {i j : I} (h : i ≠ j) (p : P i) (q : P j) :
    ¬ middle (⟨i, p⟩ : Σ i, P i) ≤ middle (⟨j, q⟩ : Σ i, P i) := by
  simpa only [middle, WithBot.coe_le_coe, WithTop.coe_le_coe] using sigma_not_le_of_ne h p q

theorem image_Iic_subset_iff {P Q : Type*} [PartialOrder P] (e : P → Q)
    (he : Function.Injective e) (p q : P) : e '' Set.Iic p ⊆ e '' Set.Iic q ↔ p ≤ q := by
  constructor
  · intro h
    obtain ⟨r, hr, hrr⟩ := h (Set.mem_image_of_mem e (show p ∈ Set.Iic p from le_rfl))
    exact he hrr ▸ hr
  · intro h
    exact Set.image_mono (Set.Iic_subset_Iic.mpr h)

/-- Countability is more than sufficient for the main theorem's exact
order-embedding hypothesis; no linear ordering of the poset is introduced. -/
def countablePosetSetEmbedding (P : Type*) [PartialOrder P] [Countable P] :
    P ↪o Set (Set ℕ) := by
  let e : P ↪ ℕ := Classical.choice (nonempty_embedding_nat P)
  let f : P → Set ℕ := fun p => {e p}
  have hf : Function.Injective f := fun p q h => e.injective (Set.singleton_injective h)
  exact {
    toFun := fun p => f '' Set.Iic p
    inj' := fun p q h => le_antisymm
      ((image_Iic_subset_iff f hf p q).mp h.le)
      ((image_Iic_subset_iff f hf q p).mp h.ge)
    map_rel_iff' := fun {p q} => image_Iic_subset_iff f hf p q }

theorem FewOperators.restrict {𝕜 : Type*} [RCLike 𝕜]
    {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    {X : Q → Type*} [∀ q, NormedAddCommGroup (X q)] [∀ q, NormedSpace 𝕜 (X q)]
    {j : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X j) (e : P ↪o Q) :
    FewOperators 𝕜 (fun p => X (e p)) (fun s t => j (e s) (e t)) := by
  refine ⟨fun p => h.1 (e p), ?_, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    exact h.2.1 _ _ (e.monotone hst)
  · intro r s t hrs hst
    exact h.2.2.1 _ _ _ (e.monotone hrs) (e.monotone hst)
  · intro s t hst
    exact h.2.2.2.1 _ _ (fun he => hst (e.le_iff_le.mp he))
  · intro s t hst T
    exact h.2.2.2.2.1 _ _ (e.monotone hst) T
  · intro s t hst T
    exact h.2.2.2.2.2 _ _ (fun he => hst (e.le_iff_le.mp he)) T

end Posets
