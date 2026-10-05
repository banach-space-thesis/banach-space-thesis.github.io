import PosetsCommon.Algebra
import Mathlib.Analysis.Normed.Ring.Units

noncomputable section
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]

/-- Algebraic two-sided linear ideals, without a closedness hypothesis. -/
def IsAlgebraIdeal (I : Set A) : Prop :=
  (0 : A) ∈ I ∧ (∀ a ∈ I, ∀ b ∈ I, a + b ∈ I) ∧
  (∀ c : 𝕜, ∀ a ∈ I, c • a ∈ I) ∧
  (∀ a : A, ∀ b ∈ I, a * b ∈ I ∧ b * a ∈ I)

def IsMaximalAlgebraIdeal (I : Set A) : Prop :=
  IsAlgebraIdeal 𝕜 I ∧ I ≠ Set.univ ∧
    ∀ J : Set A, IsAlgebraIdeal 𝕜 J → I ⊆ J → J = I ∨ J = Set.univ

variable {𝕜}

theorem IsAlgebraIdeal.isClosedIdeal_closure {I : Set A} (hI : IsAlgebraIdeal 𝕜 I) :
    IsClosedIdeal 𝕜 (closure I) := by
  let S : Submodule 𝕜 A :=
    { carrier := I, zero_mem' := hI.1,
      add_mem' := fun ha hb => hI.2.1 _ ha _ hb,
      smul_mem' := fun c a ha => hI.2.2.1 c a ha }
  refine ⟨isClosed_closure, ?_, ?_, ?_, ?_⟩
  · exact S.topologicalClosure.zero_mem
  · intro a ha b hb
    exact S.topologicalClosure.add_mem ha hb
  · intro c a ha
    exact S.topologicalClosure.smul_mem c ha
  · intro a b hb
    constructor
    · have hpre : I ⊆ (fun x : A => a * x) ⁻¹' closure I :=
        fun x hx => subset_closure (hI.2.2.2 a x hx).1
      exact closure_minimal hpre
        (isClosed_closure.preimage (continuous_const.mul continuous_id)) hb
    · have hpre : I ⊆ (fun x : A => x * a) ⁻¹' closure I :=
        fun x hx => subset_closure (hI.2.2.2 a x hx).2
      exact closure_minimal hpre
        (isClosed_closure.preimage (continuous_id.mul continuous_const)) hb

theorem IsAlgebraIdeal.eq_univ_of_unit_mem {I : Set A} (hI : IsAlgebraIdeal 𝕜 I)
    {x : A} (hx : x ∈ I) (hu : IsUnit x) : I = Set.univ := by
  obtain ⟨u, rfl⟩ := hu
  have hone : (1 : A) ∈ I := by
    simpa only [Units.inv_mul] using (hI.2.2.2 (↑u⁻¹) (↑u) hx).1
  apply Set.eq_univ_of_forall
  intro a
  simpa only [mul_one] using (hI.2.2.2 a 1 hone).1

variable [CompleteSpace A]

/-- A proper ideal cannot be dense, because units form an open neighbourhood of one. -/
theorem IsAlgebraIdeal.closure_ne_univ {I : Set A} (hI : IsAlgebraIdeal 𝕜 I)
    (hproper : I ≠ Set.univ) : closure I ≠ Set.univ := by
  intro hcl
  have hd : Dense I := by rw [dense_iff_closure_eq]; exact hcl
  obtain ⟨u, huI, hu⟩ := hd.exists_mem_open Units.isOpen ⟨1, isUnit_one⟩
  exact hproper (hI.eq_univ_of_unit_mem huI hu)

theorem isMaximalAlgebraIdeal_iff_isMaximalClosedIdeal (I : Set A) :
    IsMaximalAlgebraIdeal 𝕜 I ↔ IsMaximalClosedIdeal 𝕜 I := by
  constructor
  · rintro ⟨hI, hp, hm⟩
    have hcl : closure I = I := (hm (closure I) hI.isClosedIdeal_closure.2 subset_closure).resolve_right
      (hI.closure_ne_univ hp)
    refine ⟨⟨?_, hI⟩, hp, fun J hJ hIJ => hm J hJ.2 hIJ⟩
    rw [← hcl]
    exact isClosed_closure
  · rintro ⟨hI, hp, hm⟩
    refine ⟨hI.2, hp, ?_⟩
    intro J hJ hIJ
    by_cases hJp : J = Set.univ
    · exact Or.inr hJp
    · have hcl : closure J = I :=
        (hm (closure J) hJ.isClosedIdeal_closure (hIJ.trans subset_closure)).resolve_right
          (hJ.closure_ne_univ hJp)
      exact Or.inl (Set.Subset.antisymm (hcl ▸ subset_closure) hIJ)

theorem uniqueMaximalAlgebraIdeal_iff_uniqueMaximalClosedIdeal :
    (∃! I : Set A, IsMaximalAlgebraIdeal 𝕜 I) ↔ HasUniqueMaximalClosedIdeal 𝕜 A := by
  simp only [HasUniqueMaximalClosedIdeal, isMaximalAlgebraIdeal_iff_isMaximalClosedIdeal]

end ThesisCommon
