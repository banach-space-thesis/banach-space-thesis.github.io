import Mathlib.Topology.ClopenBox
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-! Countability of uniformly separated cuts in a compact metric image.
This is the topological counting step in Sigma Lemma 4.3. -/
noncomputable section
open Set Topology TopologicalSpace
namespace ThesisCommon

theorem countable_clopens_of_compact_secondCountable (X : Type*) [TopologicalSpace X]
    [CompactSpace X] [SecondCountableTopology X] : Countable (TopologicalSpace.Clopens X) := by
  have h (s : TopologicalSpace.Clopens X) :
      ∃ t : Finset (countableBasis X), s.1 = t.toSet.sUnion :=
    eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open _
      (isBasis_countableBasis X) s.1 s.2.1.isCompact s.2.2
  let f : TopologicalSpace.Clopens X → Finset (countableBasis X) := fun s => (h s).choose
  have hf : Function.Injective f := by
    intro s t hst
    apply SetLike.coe_injective
    change s.carrier = t.carrier
    change (h s).choose = (h t).choose at hst
    rw [(h s).choose_spec, (h t).choose_spec, hst]
  exact hf.countable

theorem disjoint_closures_of_uniform_gap {X : Type*} [PseudoMetricSpace X]
    (s t : Set X) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ x ∈ s, ∀ y ∈ t, ε ≤ dist x y) : Disjoint (closure s) (closure t) := by
  have hx (y : X) (hy : y ∈ t) : closure s ⊆ {x | ε ≤ dist x y} :=
    closure_minimal (fun x hx => hgap x hx y hy)
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hy (x : X) (hxs : x ∈ closure s) : closure t ⊆ {y | ε ≤ dist x y} :=
    closure_minimal (fun y hyt => hx y hyt hxs)
      (isClosed_le continuous_const (continuous_const.dist continuous_id))
  apply Set.disjoint_left.mpr
  intro x hxs hxt
  have hh := hy x hxs hxt
  simp only [Set.mem_setOf_eq, dist_self] at hh
  exact (not_le_of_gt hε) hh

def MetricSeparatedCut {D X : Type*} [PseudoMetricSpace X]
    (f : D → X) (M A : Set D) : Prop :=
  A ⊆ M ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ A, ∀ y ∈ M \ A, ε ≤ dist (f x) (f y)

theorem separated_cut_clopen {D X : Type*} [PseudoMetricSpace X]
    (f : D → X) (M A : Set D) (h : MetricSeparatedCut f M A) :
    IsClopen {x : ↥(closure (f '' M)) | x.val ∈ closure (f '' A)} := by
  obtain ⟨hAM, ε, hε, hgap⟩ := h
  have hdisj : Disjoint (closure (f '' A)) (closure (f '' (M \ A))) := by
    apply disjoint_closures_of_uniform_gap _ _ hε
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hgap x hx y hy
  have hunion : closure (f '' A) ∪ closure (f '' (M \ A)) = closure (f '' M) := by
    rw [← closure_union, ← Set.image_union, Set.union_diff_cancel hAM]
  have hcompl : {x : ↥(closure (f '' M)) | x.val ∈ closure (f '' A)}ᶜ =
      {x : ↥(closure (f '' M)) | x.val ∈ closure (f '' (M \ A))} := by
    ext x
    constructor
    · intro hx
      have hm : x.val ∈ closure (f '' A) ∪ closure (f '' (M \ A)) := hunion.symm ▸ x.property
      exact hm.resolve_left hx
    · intro hx ha
      exact Set.disjoint_left.mp hdisj ha hx
  refine ⟨isClosed_closure.preimage continuous_subtype_val, ?_⟩
  rw [← isClosed_compl_iff, hcompl]
  exact isClosed_closure.preimage continuous_subtype_val

theorem separated_cut_recovered {D X : Type*} [PseudoMetricSpace X]
    (f : D → X) (M A : Set D) (h : MetricSeparatedCut f M A) (x : D) (hx : x ∈ M) :
    f x ∈ closure (f '' A) ↔ x ∈ A := by
  constructor
  · intro ha
    by_contra hxa
    obtain ⟨_, ε, hε, hgap⟩ := h
    have hclosed : closure (f '' A) ⊆ {y | ε ≤ dist y (f x)} :=
      closure_minimal (by rintro _ ⟨z, hz, rfl⟩; exact hgap z hz x ⟨hx, hxa⟩)
        (isClosed_le continuous_const (continuous_id.dist continuous_const))
    have hh := hclosed ha
    simp only [Set.mem_setOf_eq, dist_self] at hh
    exact (not_le_of_gt hε) hh
  · intro ha
    exact subset_closure (Set.mem_image_of_mem f ha)

theorem metric_separated_cuts_countable {D X : Type*} [PseudoMetricSpace X]
    [CompactSpace X] [SecondCountableTopology X] (f : D → X) (M : Set D) :
    Set.Countable {A | MetricSeparatedCut f M A} := by
  let K := ↥(closure (f '' M))
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  haveI : Countable (TopologicalSpace.Clopens K) := countable_clopens_of_compact_secondCountable K
  let code : {A // MetricSeparatedCut f M A} → TopologicalSpace.Clopens K :=
    fun A => ⟨{x : K | x.val ∈ closure (f '' A.val)}, separated_cut_clopen f M A.val A.property⟩
  have hinj : Function.Injective code := by
    intro A B hab
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ M
    · have he : f x ∈ closure (f '' A.val) ↔ f x ∈ closure (f '' B.val) := by
        have hh := congrArg (fun U : TopologicalSpace.Clopens K =>
          (⟨f x, subset_closure (Set.mem_image_of_mem f hx)⟩ : K) ∈ U) hab
        exact iff_of_eq hh
      exact (separated_cut_recovered f M A.val A.property x hx).symm.trans
        (he.trans (separated_cut_recovered f M B.val B.property x hx))
    · exact iff_of_false (fun ha => hx (A.property.1 ha)) (fun hb => hx (B.property.1 hb))
  exact hinj.countable

end ThesisCommon
