import NonCalkinAlgebra.OrderInvariantFiberCounting
import NonCalkinAlgebra.AFCoefficientStatements

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.OrderInvariantCounting
universe u

theorem cardinal_union_le_of_small_fibers {M I : Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hM : Cardinal.mk M ≤ κ) (R : M → I → Prop)
    (hR : ∀ m, Cardinal.mk {i : I | R m i} ≤ κ) :
    Cardinal.mk (⋃ m : M, {i : I | R m i}) ≤ κ := by
  calc
    _ ≤ Cardinal.sum (fun m : M => Cardinal.mk {i : I | R m i}) :=
      Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : M => κ) := Cardinal.sum_le_sum _ _ hR
    _ = Cardinal.mk M * κ := Cardinal.sum_const' M κ
    _ ≤ κ * κ := mul_le_mul' hM le_rfl
    _ = κ := Cardinal.mul_eq_self hκ

/-- More than kappa candidates cannot all be covered by at most kappa models
when each model covers at most kappa candidates. No regularity is required. -/
theorem exists_avoiding_small_fibers {M I : Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hM : Cardinal.mk M ≤ κ) (hI : κ < Cardinal.mk I)
    (R : M → I → Prop) (hR : ∀ m, Cardinal.mk {i : I | R m i} ≤ κ) :
    ∃ i : I, ∀ m : M, ¬ R m i := by
  classical
  by_contra! hall
  have hcover : (⋃ m : M, {i : I | R m i}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    obtain ⟨m, hm⟩ := hall i
    exact Set.mem_iUnion.mpr ⟨m, hm⟩
  have hsmall := cardinal_union_le_of_small_fibers hκ hM R hR
  rw [hcover, Cardinal.mk_univ] at hsmall
  exact (not_le_of_gt hI) hsmall

theorem exists_large_membership_fiber_of_nonempty {A I : Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hA : Cardinal.mk A ≤ κ) (hI : κ < Cardinal.mk I)
    (s : I → Set A) (hs : ∀ i, (s i).Nonempty) :
    ∃ a : A, κ < Cardinal.mk {i : I | a ∈ s i} := by
  classical
  by_contra! hfiber
  obtain ⟨i, hi⟩ := exists_avoiding_small_fibers hκ hA hI (fun a i => a ∈ s i) hfiber
  obtain ⟨a, ha⟩ := hs i
  exact hi a ha

/-- The combinatorial outer layer of the disjoint-representing-sequence
count: coordinatewise disjoint sequences, each admitted on a nonempty set
of coordinates, are bounded by the local cardinal bound. The values may
have different types at different coordinates, as in the singular cases.
The model-theoretic hypotheses producing the local sets are separate. -/
theorem cardinal_le_of_disjoint_supported_sequences {I A : Type u} {X : A → Type u}
    {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ) (hA : Cardinal.mk A ≤ κ)
    (b : I → ∀ a : A, X a)
    (hdisjoint : ∀ i j a, b i a = b j a → i = j)
    (T : ∀ a : A, Set (X a)) (hT : ∀ a, Cardinal.mk (T a) ≤ κ)
    (S : I → Set A) (hS : ∀ i, (S i).Nonempty)
    (hmem : ∀ i a, a ∈ S i → b i a ∈ T a) : Cardinal.mk I ≤ κ := by
  classical
  by_contra! hlarge
  have hfiber : ∀ a, Cardinal.mk {i : I | a ∈ S i} ≤ κ := by
    intro a
    let f : {i : I | a ∈ S i} → T a := fun i => ⟨b i.val a, hmem i.val a i.property⟩
    have hinj : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact hdisjoint i.val j.val a (congrArg Subtype.val hij)
    exact (Cardinal.mk_le_of_injective hinj).trans (hT a)
  obtain ⟨a, ha⟩ := exists_large_membership_fiber_of_nonempty hκ hA hlarge S hS
  exact (not_le_of_gt ha) (hfiber a)

end NonCalkinAlgebra.OrderInvariantCounting

namespace NonCalkinAlgebra
open TopologicalSpace
universe v

/-- Selection can use a cardinal bound on each representation fiber instead
of first extracting a pairwise nonisomorphic family. Those fiber bounds are
explicit hypotheses here; the nonstructure theorem is not assumed silently. -/
theorem AF_coefficient_existence_of_small_model_fibers {I : Type}
    (D : I → ComplexCStarAlgebra.{0})
    (hlarge : Cardinal.continuum < Cardinal.mk I)
    (hfibers : ∀ M : SeparableCalkinModel,
      Cardinal.mk {i : I | Nonempty (M.Carrier ≃A[ℂ] (D i).Carrier)} ≤ Cardinal.continuum)
    (hAF : ∀ i, IsApproximatelyFiniteDimensional (D i).Carrier)
    (hdensity : ∀ i, HasDensityCharacter (D i).Carrier Cardinal.continuum)
    (hsimple : ∀ i, IsTopologicallySimple (D i).Carrier) :
    AFCoefficientExistenceStatement.{v} := by
  obtain ⟨i, hi⟩ := OrderInvariantCounting.exists_avoiding_small_fibers
    Cardinal.aleph0_le_continuum cardinal_separableCalkinModel_le_continuum hlarge
    (fun M i => Nonempty (M.Carrier ≃A[ℂ] (D i).Carrier)) hfibers
  refine ⟨D i, hAF i, hdensity i, hsimple i, ?_⟩
  intro k Y _ _ _ _
  rintro ⟨iso⟩
  obtain ⟨M, ⟨e⟩⟩ := exists_separableCalkinModel k Y
  exact hi M ⟨e.trans iso.toContinuousAlgEquiv⟩

end NonCalkinAlgebra
