import Sigma.HaydonEstimate
import ThesisCommon.Analysis.BooleanAdjoin

/-! Countable-scalar finite witnesses for separation after adjoining a generator. -/
noncomputable section
open Set ThesisCommon Cardinal
namespace SigmaNonprimarity

structure SeparationWitness (B Btilde : BooleanSubalgebra (Set ℕ)) where
  epsilon : ℚ
  left : List (B × B)
  right : List Btilde

def SeparationWitness.Separates {B Btilde : BooleanSubalgebra (Set ℕ)}
    (w : SeparationWitness B Btilde) (Z : Set ℕ) (M N : Set PairedMeasure) : Prop :=
  0 < w.epsilon ∧ ∀ μ ∈ M, ∀ ν ∈ N,
    (∃ i : Fin w.left.length,
      (w.epsilon : ℝ) ≤ |μ (Sum.inl '' (((w.left.get i).1.val ∩ Z) ∪ ((w.left.get i).2.val \ Z))) -
        ν (Sum.inl '' (((w.left.get i).1.val ∩ Z) ∪ ((w.left.get i).2.val \ Z)))|) ∨
    (∃ l : Fin w.right.length,
      (w.epsilon : ℝ) ≤ |μ (Sum.inr '' (w.right.get l).val) - ν (Sum.inr '' (w.right.get l).val)|)

theorem separationWitness_exists (B Btilde : BooleanSubalgebra (Set ℕ))
    (Z : Set ℕ) (M N : Set PairedMeasure)
    (h : PairedSeparated (adjoinSet B Z) Btilde M N) :
    ∃ w : SeparationWitness B Btilde, w.Separates Z M N := by
  classical
  obtain ⟨ε, hε, F, _, hgap⟩ := h
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hrepr (S : adjoinSet B Z) : ∃ p : B × B,
      S.val = (p.1.val ∩ Z) ∪ (p.2.val \ Z) := by
    obtain ⟨A, hA, D, hD, heq⟩ := (mem_adjoinSet_iff B Z S.val).mp S.property
    exact ⟨(⟨A, hA⟩, ⟨D, hD⟩), heq⟩
  choose p hp using hrepr
  let e := (Fintype.equivFin F).symm
  let a : Fin (Fintype.card F) → B × B := fun i =>
    match (e i).val with
    | .inl S => p S
    | .inr _ => (⊥, ⊥)
  let r : Fin (Fintype.card F) → Btilde := fun i =>
    match (e i).val with
    | .inl _ => ⊥
    | .inr S => S
  let w : SeparationWitness B Btilde := ⟨q, List.ofFn a, List.ofFn r⟩
  refine ⟨w, by exact_mod_cast hq0, ?_⟩
  intro μ hμ ν hν
  obtain ⟨t, ht, htest⟩ := hgap μ hμ ν hν
  let i := e.symm ⟨t, ht⟩
  have hi : (e i).val = t := congrArg Subtype.val (e.apply_symm_apply ⟨t, ht⟩)
  cases t with
  | inl S =>
    left
    refine ⟨⟨i.val, by simpa [w] using i.isLt⟩, ?_⟩
    have hg : (w.left.get ⟨i.val, by simpa [w] using i.isLt⟩) = p S := by
      simp [w, a, hi]
    change (q : ℝ) ≤ _
    rw [hg, ← hp S]
    exact hqε.le.trans htest
  | inr S =>
    right
    refine ⟨⟨i.val, by simpa [w] using i.isLt⟩, ?_⟩
    have hg : (w.right.get ⟨i.val, by simpa [w] using i.isLt⟩) = S := by
      simp [w, r, hi]
    change (q : ℝ) ≤ _
    rw [hg]
    exact hqε.le.trans htest

/-- A fixed witness can work for only finitely many members of an almost
disjoint family, unless the original algebras already separate the measures. -/
theorem SeparationWitness.finite_successes {B Btilde : BooleanSubalgebra (Set ℕ)}
    (w : SeparationWitness B Btilde)
    (hfinite : ∀ F : Set ℕ, F.Finite → F ∈ B)
    (M N : Set PairedMeasure) (hnsep : ¬ PairedSeparated B Btilde M N)
    (S : Set (Set ℕ)) (hS : S.Pairwise (fun Z W => (Z ∩ W).Finite)) :
    {Z | Z ∈ S ∧ w.Separates Z M N}.Finite := by
  classical
  by_contra h
  have hinf : {Z | Z ∈ S ∧ w.Separates Z M N}.Infinite := h
  let e := hinf.natEmbedding {Z | Z ∈ S ∧ w.Separates Z M N}
  have hq : (0 : ℝ) < w.epsilon := by exact_mod_cast (e 0).property.2.1
  obtain ⟨k, hk⟩ := exists_nat_gt (12 * (w.left.length : ℝ) / w.epsilon)
  let Z : Fin k → Set ℕ := fun j => (e j.val).val
  have hZ : Pairwise (fun i j => (Z i ∩ Z j).Finite) := by
    intro i j hij
    apply hS (e i.val).property.1 (e j.val).property.1
    intro heq
    have he : e i.val = e j.val := Subtype.ext heq
    exact hij (Fin.ext (e.injective he))
  apply hnsep
  apply haydon_finite_separation B Btilde hfinite M N
    (fun i => (w.left.get i).1) (fun i => (w.left.get i).2)
    w.right.get Z hZ w.epsilon hq hk
  intro j μ hμ ν hν
  exact (e j.val).property.2.2 μ hμ ν hν

theorem separationWitness_cardinal_le (B Btilde : BooleanSubalgebra (Set ℕ)) (κ : Cardinal)
    (hκ : ℵ₀ ≤ κ) (hB : #B ≤ κ) (hBtilde : #Btilde ≤ κ) :
    #(SeparationWitness B Btilde) ≤ κ := by
  let code : SeparationWitness B Btilde → ℚ × List (B × B) × List Btilde :=
    fun w => (w.epsilon, w.left, w.right)
  have hcode : Function.Injective code := by
    rintro ⟨q, a, r⟩ ⟨q', a', r'⟩ h
    simpa [code] using h
  have hpair : #(B × B) ≤ κ := by
    simpa using (mul_le_mul' hB hB).trans_eq (Cardinal.mul_eq_self hκ)
  have hleft : #(List (B × B)) ≤ κ := (Cardinal.mk_list_le_max _).trans (max_le hκ hpair)
  have hright : #(List Btilde) ≤ κ := (Cardinal.mk_list_le_max _).trans (max_le hκ hBtilde)
  have hrat : #ℚ ≤ κ := Cardinal.mk_le_aleph0.trans hκ
  calc
    _ ≤ #(ℚ × List (B × B) × List Btilde) := Cardinal.mk_le_of_injective hcode
    _ ≤ κ := by
      simpa using (mul_le_mul' hrat
        ((mul_le_mul' hleft hright).trans_eq (Cardinal.mul_eq_self hκ))).trans_eq
          (Cardinal.mul_eq_self hκ)

end SigmaNonprimarity
