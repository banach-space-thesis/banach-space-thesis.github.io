import Sigma.Splitting
import Mathlib.Topology.Algebra.Algebra

/-! The closed span defining JL(B) is an algebra for an almost-disjoint family. -/
noncomputable section
namespace SigmaNonprimarity

def jlGenerators (B : Set (Set Point)) : Set Ambient :=
  {f | ∃ p : Point, f = characteristic {p}} ∪
    characteristic '' B ∪ {characteristic Set.univ}

@[simp] theorem characteristic_univ : characteristic Set.univ = (1 : Ambient) := by
  ext p
  simp

theorem characteristic_mul (s t : Set Point) :
    characteristic s * characteristic t = characteristic (s ∩ t) := by
  classical
  ext p
  by_cases hs : p ∈ s <;> by_cases ht : p ∈ t <;> simp [hs, ht]

theorem singleton_mul (p : Point) (f : Ambient) :
    characteristic {p} * f = f p • characteristic {p} := by
  classical
  ext q
  by_cases h : q = p
  · subst q; simp
  · simp [h]

theorem characteristic_finset (F : Finset Point) :
    characteristic (↑F : Set Point) = ∑ p ∈ F, characteristic {p} := by
  classical
  induction F using Finset.induction with
  | empty => ext p; simp
  | @insert x F hx ih =>
    rw [Finset.sum_insert hx, ← ih]
    ext p
    by_cases hp : p = x
    · subst p; simp [hx]
    · by_cases hpF : p ∈ F <;> simp [hp, hpF]

theorem characteristic_finite_mem_span (B : Set (Set Point)) {s : Set Point} (hs : s.Finite) :
    characteristic s ∈ Submodule.span ℝ (jlGenerators B) := by
  rw [← hs.coe_toFinset, characteristic_finset]
  apply Submodule.sum_mem
  intro p _
  exact Submodule.subset_span (Or.inl (Or.inl ⟨p, rfl⟩))

theorem generator_mul_mem_span {B : Set (Set Point)} (hB : AlmostDisjoint B)
    {f g : Ambient} (hf : f ∈ jlGenerators B) (hg : g ∈ jlGenerators B) :
    f * g ∈ Submodule.span ℝ (jlGenerators B) := by
  classical
  rcases hf with (⟨p, rfl⟩ | ⟨b, hb, rfl⟩) | rfl
  · rw [singleton_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inl ⟨p, rfl⟩)))
  · rcases hg with (⟨p, rfl⟩ | ⟨c, hc, rfl⟩) | rfl
    · rw [mul_comm, singleton_mul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inl ⟨p, rfl⟩)))
    · rw [characteristic_mul]
      by_cases hbc : b = c
      · subst c
        rw [Set.inter_self]
        exact Submodule.subset_span (Or.inl (Or.inr ⟨b, hb, rfl⟩))
      · exact characteristic_finite_mem_span B (hB.2 b hb c hc hbc)
    · rw [characteristic_univ, mul_one]
      exact Submodule.subset_span (Or.inl (Or.inr ⟨b, hb, rfl⟩))
  · rw [characteristic_univ, one_mul]
    exact Submodule.subset_span hg

theorem span_mul_mem {B : Set (Set Point)} (hB : AlmostDisjoint B) {f g : Ambient}
    (hf : f ∈ Submodule.span ℝ (jlGenerators B))
    (hg : g ∈ Submodule.span ℝ (jlGenerators B)) :
    f * g ∈ Submodule.span ℝ (jlGenerators B) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    induction hg using Submodule.span_induction with
    | mem g hg => exact generator_mul_mem_span hB hf hg
    | zero => simpa using (Submodule.span ℝ (jlGenerators B)).zero_mem
    | add x y _ _ hx hy => simpa [mul_add] using Submodule.add_mem _ hx hy
    | smul r x _ hx => simpa [mul_smul_comm] using Submodule.smul_mem _ r hx
  | zero => simpa using (Submodule.span ℝ (jlGenerators B)).zero_mem
  | add x y _ _ hx hy => simpa [add_mul] using Submodule.add_mem _ hx hy
  | smul r x _ hx => simpa [smul_mul_assoc] using Submodule.smul_mem _ r hx

def jlSpanAlgebra {B : Set (Set Point)} (hB : AlmostDisjoint B) : Subalgebra ℝ Ambient :=
  (Submodule.span ℝ (jlGenerators B)).toSubalgebra
    (by rw [← characteristic_univ]; exact Submodule.subset_span (Or.inr rfl))
    (fun _ _ hf hg => span_mul_mem hB hf hg)

def jlAlgebra {B : Set (Set Point)} (hB : AlmostDisjoint B) : Subalgebra ℝ Ambient :=
  (jlSpanAlgebra hB).topologicalClosure

theorem jlAlgebra_toSubmodule {B : Set (Set Point)} (hB : AlmostDisjoint B) :
    (jlAlgebra hB).toSubmodule = JL B := rfl

theorem mul_mem_JL {B : Set (Set Point)} (hB : AlmostDisjoint B)
    {f g : Ambient} (hf : f ∈ JL B) (hg : g ∈ JL B) : f * g ∈ JL B :=
  (jlAlgebra hB).mul_mem hf hg

end SigmaNonprimarity
