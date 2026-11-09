import NonCalkinAlgebra.ProductBlockDiagram
import NonCalkinAlgebra.FiniteProductSums
import NonCalkinAlgebra.BlockTraceCompatibility

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
open NonCalkinAlgebra.FiniteBlockRefinement

universe u
variable {ι : Type u} (D : ι → RootedBlockDiagram.{u})

instance localColorFintype (B : RootedBlockDiagram.{u}) (n : ℕ) :
    Fintype (B.Color n) := Fintype.ofFinite _

instance localPathCopiesFintype (B : RootedBlockDiagram.{u}) (a b : ℕ) (h : a ≤ b)
    (d : B.Color b) : Fintype ((B.path a b h).Copies d) :=
  Fintype.ofFinite _

variable (w : ∀ i n, (D i).Color n → ℝ)

/-- Weights multiply across the active coordinates of a product stage. -/
def tensorWeight (a : Level ι) (c : TensorColor D a) : ℝ :=
  ∏ i ∈ a.support, w i (a i) (c i)

theorem tensorWeight_mem (S : Subring ℝ) (hw : ∀ i n c, w i n c ∈ S)
    (a : Level ι) (c : TensorColor D a) : tensorWeight D w a c ∈ S :=
  S.prod_mem fun i _ => hw i (a i) (c i)

theorem tensorWeight_nonneg (hw : ∀ i n c, 0 ≤ w i n c)
    (a : Level ι) (c : TensorColor D a) : 0 ≤ tensorWeight D w a c :=
  Finset.prod_nonneg fun i _ => hw i (a i) (c i)

theorem tensorWeight_law
    (hw0 : ∀ i c, w i 0 c = 1)
    (hw : ∀ i a b (h : a ≤ b), ((D i).path a b h).WeightLaw (w i a) (w i b))
    (a b : Level ι) (hab : a ≤ b) :
    (tensorRefinement D a b hab).WeightLaw (tensorWeight D w a) (tensorWeight D w b) := by
  classical
  intro c
  let f i := (D i).path (a i) (b i) (hab i)
  let A i := Σ d : (D i).Color (b i), (f i).Copies d
  letI (i : ι) : Fintype (A i) :=
    inferInstanceAs (Fintype (Σ d : (D i).Color (b i), ((D i).path (a i) (b i) (hab i)).Copies d))
  letI (i : ι) : Nonempty (A i) := by
    let d : (D i).Color (b i) := Classical.choice inferInstance
    exact ⟨⟨d, Classical.choice (inferInstance : Nonempty (((D i).path (a i) (b i) (hab i)).Copies d))⟩⟩
  let e : (Σ d : TensorColor D b, (tensorRefinement D a b hab).Copies d) ≃ (∀ i, A i) :=
    productSigma
  letI : Fintype (∀ i, A i) := Fintype.ofEquiv _ e
  have hzero (i : ι) (hi : i ∉ b.support) : a i = 0 ∧ b i = 0 := by
    have hb : b i = 0 := Finsupp.notMem_support_iff.mp hi
    exact ⟨Nat.eq_zero_of_le_zero (hb ▸ hab i), hb⟩
  have hsingle (i : ι) (hi : i ∉ b.support) : Subsingleton (A i) := by
    obtain ⟨ha, hb⟩ := hzero i hi
    have aux (n m : ℕ) (hn : n = 0) (hm : m = 0) (h : n ≤ m) :
        Subsingleton (Σ d : (D i).Color m, ((D i).path n m h).Copies d) := by
      subst n
      subst m
      rw [(D i).path_self]
      change Subsingleton (Σ _ : (D i).Color 0, PUnit)
      constructor
      rintro ⟨d, ⟨⟩⟩ ⟨d', ⟨⟩⟩
      have hd : d = d' := Subsingleton.elim _ _
      subst d'
      rfl
    exact aux _ _ ha hb (hab i)
  let v (i : ι) (z : A i) := if (f i).color z.1 z.2 = c i then w i (b i) z.1 else 0
  have hproduct (z : Σ d : TensorColor D b, (tensorRefinement D a b hab).Copies d) :
      (if (tensorRefinement D a b hab).color z.1 z.2 = c then tensorWeight D w b z.1 else 0) =
        ∏ i ∈ b.support, v i (e z i) := by
    by_cases hc : (tensorRefinement D a b hab).color z.1 z.2 = c
    · rw [if_pos hc]
      apply Finset.prod_congr rfl
      intro i _
      exact (if_pos (congrFun hc i)).symm
    · rw [if_neg hc]
      have hbad : ∃ i ∈ b.support, (f i).color (e z i).1 (e z i).2 ≠ c i := by
        by_contra! hh
        apply hc
        funext i
        by_cases hi : i ∈ b.support
        · exact hh i hi
        · have ha := (hzero i hi).1
          haveI : Subsingleton ((D i).Color (a i)) := by rw [ha]; infer_instance
          exact Subsingleton.elim _ _
      obtain ⟨i, hi, hne⟩ := hbad
      exact (Finset.prod_eq_zero hi (if_neg hne)).symm
  have hsum (i : ι) : (∑ z : A i, v i z) = w i (a i) (c i) := by
    rw [Fintype.sum_sigma]
    exact hw i (a i) (b i) (hab i) (c i)
  have hsubset : a.support ⊆ b.support := by
    intro i hi
    by_contra hn
    exact (Finsupp.notMem_support_iff.mpr (hzero i hn).1) hi
  calc
    _ = ∑ z : Σ d : TensorColor D b, (tensorRefinement D a b hab).Copies d,
        if (tensorRefinement D a b hab).color z.1 z.2 = c then tensorWeight D w b z.1 else 0 :=
      (Fintype.sum_sigma _).symm
    _ = ∑ z : Σ d : TensorColor D b, (tensorRefinement D a b hab).Copies d,
        ∏ i ∈ b.support, v i (e z i) := Finset.sum_congr rfl fun z _ => hproduct z
    _ = ∑ z : ∀ i, A i, ∏ i ∈ b.support, v i (z i) := e.sum_comp (fun z : ∀ i, A i => ∏ i ∈ b.support, v i (z i))
    _ = ∏ i ∈ b.support, ∑ z : A i, v i z := sum_product_factors b.support hsingle v
    _ = ∏ i ∈ b.support, w i (a i) (c i) := Finset.prod_congr rfl fun i _ => hsum i
    _ = tensorWeight D w a c := by
      symm
      apply Finset.prod_subset hsubset
      intro i _ hi
      have hroot (n : ℕ) (hn : n = 0) (d : (D i).Color n) : w i n d = 1 := by
        subst n
        exact hw0 i d
      exact hroot (a i) (Finsupp.notMem_support_iff.mp hi) (c i)

end NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
