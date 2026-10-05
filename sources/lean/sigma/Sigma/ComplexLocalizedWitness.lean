import Sigma.ComplexLocalizedEstimate
import Sigma.LocalizedWitness

/-! Complex uses of the already defined LocalSeparationWitness. Its code is
scalar-independent; in particular its existing cardinal bound is reused. -/
noncomputable section
open Set ThesisCommon Cardinal
namespace SigmaNonprimarity

def LocalSeparationWitness.ComplexSeparates {B Btilde : BooleanSubalgebra (Set ℕ)}
    (w : LocalSeparationWitness B Btilde) (C : Set ℕ) (M N : Set ComplexPairedMeasure) : Prop :=
  0 < w.epsilon ∧ ∃ A : Fin w.outside.length → Set ℕ, ∀ μ ∈ M, ∀ ν ∈ N,
    (∃ i : Fin w.outside.length,
      (w.epsilon : ℝ) ≤ ‖μ (Sum.inl '' ((A i ∩ C) ∪ ((w.outside.get i).val \ C))) -
        ν (Sum.inl '' ((A i ∩ C) ∪ ((w.outside.get i).val \ C)))‖) ∨
    (∃ l : Fin w.right.length,
      (w.epsilon : ℝ) ≤ ‖μ (Sum.inr '' (w.right.get l).val) - ν (Sum.inr '' (w.right.get l).val)‖)

theorem complex_localSeparationWitness_exists (B Btilde : BooleanSubalgebra (Set ℕ))
    (C : Set ℕ) (M N : Set ComplexPairedMeasure)
    (h : ComplexPairedSeparated (localizedAlgebra B C) Btilde M N) :
    ∃ w : LocalSeparationWitness B Btilde, w.ComplexSeparates C M N := by
  classical
  obtain ⟨ε,hε,F,_,hgap⟩ := h
  obtain ⟨q,hq0,hqε⟩ := exists_rat_btwn hε
  have hrepr (S : localizedAlgebra B C) : ∃ p : Set ℕ × B,
      S.val = (p.1 ∩ C) ∪ (p.2.val \ C) := by
    obtain ⟨A,D,hD,heq⟩ := S.property
    exact ⟨(A,⟨D,hD⟩),heq⟩
  choose p hp using hrepr
  let e := (Fintype.equivFin F).symm
  let a : Fin (Fintype.card F) → Set ℕ := fun i =>
    match (e i).val with
    | .inl S => (p S).1
    | .inr _ => ∅
  let d : Fin (Fintype.card F) → B := fun i =>
    match (e i).val with
    | .inl S => (p S).2
    | .inr _ => ⊥
  let r : Fin (Fintype.card F) → Btilde := fun i =>
    match (e i).val with
    | .inl _ => ⊥
    | .inr S => S
  let w : LocalSeparationWitness B Btilde := ⟨q,List.ofFn d,List.ofFn r⟩
  let A : Fin w.outside.length → Set ℕ := fun i => a ⟨i.val,by simpa [w] using i.isLt⟩
  refine ⟨w,by exact_mod_cast hq0,A,?_⟩
  intro μ hμ ν hν
  obtain ⟨t,ht,htest⟩ := hgap μ hμ ν hν
  let i := e.symm ⟨t,ht⟩
  have hi : (e i).val = t := congrArg Subtype.val (e.apply_symm_apply ⟨t,ht⟩)
  cases t with
  | inl S =>
    left
    refine ⟨⟨i.val,by simpa [w] using i.isLt⟩,?_⟩
    have hd : (w.outside.get ⟨i.val,by simpa [w] using i.isLt⟩) = (p S).2 := by simp [w,d,hi]
    have ha : A ⟨i.val,by simpa [w] using i.isLt⟩ = (p S).1 := by simp [A,a,hi]
    change (q : ℝ) ≤ _
    rw [hd,ha,← hp S]
    exact hqε.le.trans htest
  | inr S =>
    right
    refine ⟨⟨i.val,by simpa [w] using i.isLt⟩,?_⟩
    have hg : (w.right.get ⟨i.val,by simpa [w] using i.isLt⟩) = S := by simp [w,r,hi]
    change (q : ℝ) ≤ _
    rw [hg]
    exact hqε.le.trans htest

theorem LocalSeparationWitness.complex_finite_successes {B Btilde : BooleanSubalgebra (Set ℕ)}
    (w : LocalSeparationWitness B Btilde)
    (hfinite : ∀ F : Set ℕ, F.Finite → F ∈ B)
    (M N : Set ComplexPairedMeasure) (hnsep : ¬ ComplexPairedSeparated B Btilde M N)
    (S : Set (Set ℕ)) (hS : S.Pairwise (fun C D => (C ∩ D).Finite)) :
    {C | C ∈ S ∧ w.ComplexSeparates C M N}.Finite := by
  classical
  by_contra h
  have hinf : {C | C ∈ S ∧ w.ComplexSeparates C M N}.Infinite := h
  let e := hinf.natEmbedding {C | C ∈ S ∧ w.ComplexSeparates C M N}
  have hq : (0 : ℝ) < w.epsilon := by exact_mod_cast (e 0).property.2.1
  obtain ⟨k,hk⟩ := exists_nat_gt (12*(w.outside.length : ℝ)/w.epsilon)
  let C : Fin k → Set ℕ := fun j => (e j.val).val
  let A : Fin k → Fin w.outside.length → Set ℕ := fun j => (e j.val).property.2.2.choose
  have hC : Pairwise (fun i j => (C i ∩ C j).Finite) := by
    intro i j hij
    apply hS (e i.val).property.1 (e j.val).property.1
    intro heq
    exact hij (Fin.ext (e.injective (Subtype.ext heq)))
  apply hnsep
  apply complex_localized_finite_separation B Btilde hfinite M N A w.outside.get
    w.right.get C hC w.epsilon hq hk
  intro j μ hμ ν hν
  exact (e j.val).property.2.2.choose_spec μ hμ ν hν

end SigmaNonprimarity
