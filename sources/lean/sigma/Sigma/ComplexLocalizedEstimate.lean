import Sigma.ComplexMeasureSeparation
import ThesisCommon.Analysis.SigmaComplexLocalizedVariation
import ThesisCommon.Analysis.HaydonFinite

/-! Complex separation estimate for arbitrary changes inside almost-disjoint
supports. This retains the printed constant 12 and removes finite overlaps. -/
noncomputable section
open Set ThesisCommon
namespace SigmaNonprimarity

theorem complex_localized_finite_separation (B Btilde : BooleanSubalgebra (Set ℕ))
    (hfinite : ∀ F : Set ℕ, F.Finite → F ∈ B)
    (M N : Set ComplexPairedMeasure) {n m k : ℕ}
    (A : Fin k → Fin n → Set ℕ) (D : Fin n → B) (R : Fin m → Btilde) (Z : Fin k → Set ℕ)
    (hZ : Pairwise (fun i j => (Z i ∩ Z j).Finite))
    (ε : ℝ) (hε : 0 < ε) (hk : 12 * (n : ℝ) / ε < (k : ℝ))
    (hnew : ∀ j, ∀ μ ∈ M, ∀ ν ∈ N,
      (∃ i, ε ≤ ‖μ (Sum.inl '' ((A j i) ∩ Z j ∪ ((D i).val \ Z j))) -
        ν (Sum.inl '' ((A j i) ∩ Z j ∪ ((D i).val \ Z j)))‖) ∨
      (∃ l, ε ≤ ‖μ (Sum.inr '' (R l).val) - ν (Sum.inr '' (R l).val)‖)) :
    ComplexPairedSeparated B Btilde M N := by
  classical
  obtain ⟨F,hF,hdisj⟩ := finite_disjoint_remainders Z hZ
  let oldD : Fin n → B ⊕ Btilde := fun i => Sum.inl (D i)
  let oldAF : Fin k × Fin n → B ⊕ Btilde := fun p =>
    Sum.inl ⟨((A p.1 p.2) ∩ Z p.1) ∩ F,hfinite _ (hF.subset Set.inter_subset_right)⟩
  let oldDF : Fin k × Fin n → B ⊕ Btilde := fun p =>
    Sum.inl ⟨((D p.2).val ∩ Z p.1) ∩ F,hfinite _ (hF.subset Set.inter_subset_right)⟩
  let oldR : Fin m → B ⊕ Btilde := fun l => Sum.inr (R l)
  let T : Set (B ⊕ Btilde) := range oldD ∪ range oldAF ∪ range oldDF ∪ range oldR
  have hT : T.Finite := ((Set.finite_range oldD).union (Set.finite_range oldAF)).union
    (Set.finite_range oldDF) |>.union (Set.finite_range oldR)
  by_contra hnsep
  unfold ComplexPairedSeparated ComplexFinitelySeparated at hnsep
  push_neg at hnsep
  obtain ⟨μ,hμ,ν,hν,hclose⟩ := hnsep (ε/6) (by positivity) hT.toFinset (Set.subset_univ _)
  have hcloseT (t : B ⊕ Btilde) (ht : t ∈ T) :
      ‖μ (pairedTest B Btilde t) - ν (pairedTest B Btilde t)‖ < ε/6 :=
    hclose t (hT.mem_toFinset.mpr ht)
  have hD (i : Fin n) : ‖complexLeftMeasure μ (D i).val - complexLeftMeasure ν (D i).val‖ < ε/6 := by
    exact hcloseT (oldD i) (by simp only [T,Set.mem_union]; exact Or.inl (Or.inl (Or.inl ⟨i,rfl⟩)))
  have hAF (j : Fin k) (i : Fin n) :
      ‖complexLeftMeasure μ (((A j i) ∩ Z j) ∩ F) -
        complexLeftMeasure ν (((A j i) ∩ Z j) ∩ F)‖ < ε/6 := by
    exact hcloseT (oldAF (j,i)) (by simp only [T,Set.mem_union]; exact Or.inl (Or.inl (Or.inr ⟨(j,i),rfl⟩)))
  have hDF (j : Fin k) (i : Fin n) :
      ‖complexLeftMeasure μ (((D i).val ∩ Z j) ∩ F) -
        complexLeftMeasure ν (((D i).val ∩ Z j) ∩ F)‖ < ε/6 := by
    exact hcloseT (oldDF (j,i)) (by simp only [T,Set.mem_union]; exact Or.inl (Or.inr ⟨(j,i),rfl⟩))
  have hR (l : Fin m) : ‖μ (Sum.inr '' (R l).val) - ν (Sum.inr '' (R l).val)‖ < ε/6 := by
    exact hcloseT (oldR l) (by simp only [T,Set.mem_union]; exact Or.inr ⟨l,rfl⟩)
  have hsize : 8 * (n : ℝ) < (k : ℝ) * ε := by
    have hh := (div_lt_iff₀ hε).mp hk
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨j,hj⟩ := (complexLeftMeasure μ).exists_close_localized (complexLeftMeasure ν)
    A (fun i => (D i).val) Z F hdisj ε hsize hD hAF hDF
  obtain ⟨i,hi⟩ | ⟨l,hl⟩ := hnew j μ hμ ν hν
  · exact (not_le_of_gt (hj i)) hi
  · linarith [hR l]

end SigmaNonprimarity
