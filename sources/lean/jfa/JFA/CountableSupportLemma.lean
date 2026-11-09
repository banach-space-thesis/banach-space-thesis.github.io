import JFA.CoordinateLemmas
import JFA.MrowkaCountableSplit
import JFA.MrowkaSupport

/-! Lemma 4.5 for a compact metric factor, using the countable-support split
on each section of the function. -/

noncomputable section
open Set TopologicalSpace
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

private theorem isSeparable_mrowka_vanishing_outside (h𝒜 : IsAlmostDisjoint 𝒜)
    (S : Set 𝒜) (hS : S.Countable) :
    IsSeparable {f : MrowkaCZero 𝕜 𝒜 | ∀ A ∉ S, f (Sum.inr A) = 0} := by
  letI := mrowka_t2Space h𝒜
  letI := mrowka_locallyCompactSpace (𝒜 := 𝒜)
  letI : TopologicalSpace PUnit.{1} := ⊥
  letI : DiscreteTopology PUnit.{1} := ⟨rfl⟩
  letI : Countable S := hS.to_subtype
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  letI : SeparableSpace C₀(PUnit.{1} × ℕ, 𝕜) := czero_countable_discrete_separable
  letI : SeparableSpace C₀(PUnit.{1} × S, 𝕜) := czero_countable_discrete_separable
  let join := mrowkaSupportJoin (𝕜 := 𝕜) (D := PUnit.{1}) S h𝒜
  let split := mrowkaSupportSplit (𝕜 := 𝕜) (D := PUnit.{1}) S h𝒜
  let curry := czeroProductEquiv (𝕜 := 𝕜) (M := PUnit.{1}) (L := Mrowka 𝒜)
  let j := (ContinuousMap.evalCLM 𝕜 (PUnit.unit : PUnit.{1})).comp
    (curry.toContinuousLinearEquiv.toContinuousLinearMap.comp join)
  apply (isSeparable_range j.continuous).mono
  intro f hf
  let g : C₀(PUnit.{1} × Mrowka 𝒜, 𝕜) :=
    czeroProductUncurry (ContinuousMap.const PUnit.{1} f)
  let g' : mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := PUnit.{1}) S :=
    ⟨g, fun _ A hA => hf A hA⟩
  refine ⟨split g', ?_⟩
  have h := congrArg (fun B => B g')
    (mrowkaSupportJoin_split (𝕜 := 𝕜) (D := PUnit.{1}) S h𝒜)
  change czeroProductSlice (join (split g')) PUnit.unit = f
  rw [show join (split g') = g from h]
  ext p
  rfl

/-- Lemma 4.5. Here separability is for the given closed subspace with its
inherited norm, and s(W) is the union of the supports of its functions. -/
theorem lemma_4_5 {M : Type*} [MetricSpace M] [CompactSpace M]
    (h𝒜 : IsAlmostDisjoint 𝒜) (W : Submodule 𝕜 C₀(M × Mrowka 𝒜, 𝕜))
    (_hW : IsClosed (W : Set C₀(M × Mrowka 𝒜, 𝕜))) :
    SeparableSpace W ↔ (mrowkaSetSupport (W : Set C₀(M × Mrowka 𝒜, 𝕜))).Countable := by
  constructor
  · intro h
    letI := h
    exact mrowka_set_support_countable (IsSeparable.of_subtype _)
  · intro hS
    letI := mrowka_t2Space h𝒜
    letI := mrowka_locallyCompactSpace (𝒜 := 𝒜)
    let S := mrowkaSetSupport (W : Set C₀(M × Mrowka 𝒜, 𝕜))
    let e := czeroProductEquiv (𝕜 := 𝕜) (M := M) (L := Mrowka 𝒜)
    let V := W.map e.toLinearEquiv.toLinearMap
    obtain ⟨D, hD, hd⟩ := exists_countable_dense M
    have hV : IsSeparable (V : Set C(M, MrowkaCZero 𝕜 𝒜)) := by
      apply (lemma_3_7 D hD hd V).mpr
      intro m _
      apply (isSeparable_mrowka_vanishing_outside (𝕜 := 𝕜) h𝒜 S hS).mono
      rintro z ⟨g, hg, rfl⟩ A hA
      obtain ⟨f, hf, rfl⟩ := (Submodule.mem_map.mp hg)
      change f (m, Sum.inr A) = 0
      by_contra hne
      exact hA ⟨f, hf, m, hne⟩
    suffices h : IsSeparable (W : Set C₀(M × Mrowka 𝒜, 𝕜)) from h.separableSpace
    apply (hV.image e.symm.continuous).mono
    intro f hf
    exact ⟨e f, Submodule.mem_map.mpr ⟨f, hf, rfl⟩, e.symm_apply_apply f⟩

end JFA
