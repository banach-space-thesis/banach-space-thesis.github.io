import Sigma.ComplexAdaptiveState
import Sigma.TransfiniteConstruction

/-! The Section 5 recursion with history-dependent charge factories. The stored
charges at a stage are exactly those computed from the eventual earlier history. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

theorem complex_exists_adaptive_construction {I : Type} [LinearOrder I] [WellFoundedLT I]
    (μ μtilde : I → ComplexAtomicRows) (R Rtilde : I → Set ℕ)
    (factory : ∀ a, (∀ b, b < a → ComplexCodedStage (μ b) (μtilde b) (R b) (Rtilde b)) → ComplexChargeSequences)
    (hsmall : ∀ a : I, #(Set.Iio a) < 𝔠)
    (hμ : ∀ a, ComplexAdmissible (μ a)) (hμt : ∀ a, ComplexAdmissible (μtilde a))
    (hR : ∀ a, (R a).Infinite) (hRt : ∀ a, (Rtilde a).Infinite) :
    ∃ d : ComplexCodedConstruction μ μtilde R Rtilde,
      d.Good Set.univ ∧ (∀ a, d.Good (Set.Iic a)) ∧
      ∀ a, (d a).measures = factory a (fun b _ => d b) := by
  classical
  let D : I → Type := fun a => ComplexCodedStage (μ a) (μtilde a) (R a) (Rtilde a)
  let Bbase := stageAlgebra (fun _ : Unit => fun _ : Bool => (∅ : Set ℕ)) ∅
  have hbase : #Bbase < 𝔠 := by
    apply (stageAlgebra_cardinal_le _ _ ℵ₀ le_rfl (by simp)).trans_lt Cardinal.aleph0_lt_continuum
  have hne (a : I) : Nonempty (D a) := by
    obtain ⟨d,_⟩ := complex_exists_threeLevelChoice_pairedNonseparated (R a) (hR a) (μ a) (hμ a) 0
      Bbase Bbase hbase hbase
    obtain ⟨dt,_⟩ := complex_exists_threeLevelChoice_pairedNonseparated (Rtilde a) (hRt a) (μtilde a) (hμt a) 0
      Bbase Bbase hbase hbase
    exact ⟨⟨(d,dt),(0,0)⟩⟩
  let fallback : ∀ a, D a := fun a => @Classical.arbitrary (D a) (hne a)
  let P : ∀ a, (∀ b, b < a → D b) → D a → Prop := fun a f x =>
    x.measures = factory a f ∧ ComplexCodedConstruction.Good (historyThrough fallback a f x) (Set.Iic a)
  have hstep (a : I) (f : ∀ b, b < a → D b)
      (ih : ∀ b (hba : b < a), P b (fun c hcb => f c (lt_trans hcb hba)) (f b hba)) :
      ∃ x, P a f x := by
    let past : ComplexCodedConstruction μ μtilde R Rtilde := fun b => if h : b < a then f b h else fallback b
    have hpast (b : I) (hb : b < a) : past b = f b hb := dif_pos hb
    have hprev (b : Set.Iio a) : past.Good (Set.Iic b.val) := by
      apply (ComplexCodedConstruction.good_congr
        (historyThrough fallback b.val (fun c hcb => f c (lt_trans hcb b.property)) (f b.val b.property))
        past (Set.Iic b.val) ?_).mp (ih b.val b.property).2
      intro c hc
      by_cases hcb : c = b.val
      · subst c
        rw [historyThrough_self, hpast _ b.property]
      · have hlt : c < b.val := lt_of_le_of_ne hc hcb
        rw [historyThrough_lt _ _ _ _ hlt, hpast _ (lt_trans hlt b.property)]
    have hdir : Directed (· ⊆ ·) (fun b : Set.Iio a => Set.Iic b.val) := by
      intro b c
      refine ⟨⟨max b.val c.val, max_lt b.property c.property⟩, ?_, ?_⟩
      · intro j hj
        exact hj.trans (le_max_left _ _)
      · intro j hj
        exact hj.trans (le_max_right _ _)
    have hcover : (⋃ b : Set.Iio a, Set.Iic b.val) = Set.Iio a := by
      ext b
      constructor
      · intro hb
        obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hb
        exact lt_of_le_of_lt hc c.property
      · intro hb
        exact Set.mem_iUnion.mpr ⟨⟨b,hb⟩,le_rfl⟩
    have hgood : past.Good (Set.Iio a) := by
      rw [← hcover]
      exact past.good_directed_union _ hdir hprev
    obtain ⟨x,hx,hgoodx⟩ := complex_exists_codedConstruction_insert past (Set.Iio a) a
      (lt_irrefl a) (hsmall a) hgood (hR a) (hRt a) (hμ a) (hμt a) (factory a f)
    have hset : insert a (Set.Iio a) = Set.Iic a := by
      ext b
      exact le_iff_eq_or_lt.symm
    refine ⟨x,hx,?_⟩
    change ComplexCodedConstruction.Good (Function.update past a x) (Set.Iic a)
    rwa [hset] at hgoodx
  obtain ⟨d,hd⟩ := wellFounded_history_choice wellFounded_lt (fun _ _ _ => lt_trans)
    D hne P hstep
  have hstages (a : I) : ComplexCodedConstruction.Good d (Set.Iic a) := by
    apply (ComplexCodedConstruction.good_congr (historyThrough fallback a (fun b _ => d b) (d a))
      d (Set.Iic a) ?_).mp (hd a).2
    intro b hb
    by_cases hba : b = a
    · subst b
      exact historyThrough_self _ _ _ _
    · exact historyThrough_lt _ _ _ _ (lt_of_le_of_ne hb hba)
  have hdir : Directed (· ⊆ ·) (fun a : I => Set.Iic a) := by
    intro a b
    exact ⟨max a b, fun _ h => h.trans (le_max_left _ _), fun _ h => h.trans (le_max_right _ _)⟩
  have hcover : (⋃ a : I, Set.Iic a) = Set.univ := by
    ext a
    exact ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_iUnion.mpr ⟨a,le_rfl⟩⟩
  refine ⟨d,?_,hstages,fun a => (hd a).1⟩
  rw [← hcover]
  exact ComplexCodedConstruction.good_directed_union d _ hdir hstages

theorem complex_exists_adaptive_continuum_construction
    (μ μtilde : ConstructionIndex → ComplexAtomicRows) (R Rtilde : ConstructionIndex → Set ℕ)
    (factory : ∀ a, (∀ b, b < a → ComplexCodedStage (μ b) (μtilde b) (R b) (Rtilde b)) → ComplexChargeSequences)
    (hμ : ∀ a, ComplexAdmissible (μ a)) (hμt : ∀ a, ComplexAdmissible (μtilde a))
    (hR : ∀ a, (R a).Infinite) (hRt : ∀ a, (Rtilde a).Infinite) :
    ∃ d : ComplexCodedConstruction μ μtilde R Rtilde,
      d.Good Set.univ ∧ (∀ a, d.Good (Set.Iic a)) ∧
      ∀ a, (d a).measures = factory a (fun b _ => d b) :=
  complex_exists_adaptive_construction μ μtilde R Rtilde factory Cardinal.mk_Iio_ord_toType hμ hμt hR hRt

end SigmaNonprimarity
