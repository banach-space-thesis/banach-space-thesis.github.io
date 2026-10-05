import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.Order.Lattice
import Mathlib.Order.BooleanSubalgebra

/-! Completion of actual dense partial isomorphisms.  A metric isomorphism
between dense subspaces extends to the complete spaces.  For Boolean
subalgebras the extension is an actual Boolean order isomorphism, proved by
continuity of meet.  This is the completion step of a back-and-forth argument;
it does not assume or assert existence of the dense partial isomorphism. -/
noncomputable section
open Set
namespace ThesisCommon
variable {A B : Type*} [MetricSpace A] [MetricSpace B]
  [CompleteSpace A] [CompleteSpace B]

theorem exists_isometryEquiv_extension_of_dense
    {s : Set A} {t : Set B} (hs : Dense s) (ht : Dense t) (e : s ≃ᵢ t) :
    ∃ g : A ≃ᵢ B, ∀ a : s, g a.val = (e a).val := by
  let f : s → B := fun a => (e a).val
  have hf : Isometry f := isometry_subtype_coe.comp e.isometry
  let g : A → B := hs.extend f
  have hg : Continuous g := (hs.uniformContinuous_extend hf.uniformContinuous).continuous
  have hge (a : s) : g a.val = f a := hs.extend_eq hf.continuous a
  have hgi : Isometry g := by
    apply Isometry.of_dist_eq
    intro x y
    refine hs.denseRange_val.induction_on₂
      (p := fun x y => dist (g x) (g y) = dist x y) ?_ ?_ x y
    · exact isClosed_eq
        ((hg.comp continuous_fst).dist (hg.comp continuous_snd))
        (continuous_fst.dist continuous_snd)
    · intro a b
      rw [hge, hge, hf.dist_eq]
      rfl
  have hdg : DenseRange g := by
    apply ht.mono
    intro y hy
    obtain ⟨a, ha⟩ := e.surjective ⟨y, hy⟩
    refine ⟨a.val, ?_⟩
    rw [hge]
    exact congrArg Subtype.val ha
  have hgs : Function.Surjective g := by
    intro y
    have hy := hdg y
    rwa [hgi.isClosedEmbedding.isClosed_range.closure_eq] at hy
  exact ⟨{ Equiv.ofBijective g ⟨hgi.injective, hgs⟩ with isometry_toFun := hgi }, hge⟩

theorem exists_booleanOrderIso_extension_of_dense
    [BooleanAlgebra A] [BooleanAlgebra B] [ContinuousInf A] [ContinuousInf B]
    (S : BooleanSubalgebra A) (T : BooleanSubalgebra B)
    (hS : Dense (S : Set A)) (hT : Dense (T : Set B))
    (e : S ≃o T) (he : Isometry e) :
    ∃ g : A ≃o B, Isometry g ∧ ∀ a : S, g a.val = (e a).val := by
  obtain ⟨g, hge⟩ := exists_isometryEquiv_extension_of_dense hS hT
    ({ e.toEquiv with isometry_toFun := he } : S ≃ᵢ T)
  have hginf : ∀ a b : A, g (a ⊓ b) = g a ⊓ g b := by
    intro x y
    refine hS.denseRange_val.induction_on₂
      (p := fun a b => g (a ⊓ b) = g a ⊓ g b) ?_ ?_ x y
    · exact isClosed_eq (g.continuous.comp continuous_inf)
        ((g.continuous.comp continuous_fst).inf (g.continuous.comp continuous_snd))
    · intro a b
      change g (a ⊓ b : S).val = g a.val ⊓ g b.val
      rw [hge, hge, hge]
      exact congrArg Subtype.val (e.map_inf a b)
  let G : A ≃o B :=
    { g.toEquiv with
      map_rel_iff' := by
        intro a b
        change g a ≤ g b ↔ a ≤ b
        rw [← inf_eq_left, ← hginf, g.injective.eq_iff, inf_eq_left] }
  exact ⟨G, g.isometry, hge⟩

end ThesisCommon
