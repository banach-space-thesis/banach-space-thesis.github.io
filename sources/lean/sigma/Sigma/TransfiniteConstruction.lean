import Sigma.ConstructionLimit
import Sigma.ConstructionSuccessor
import ThesisCommon.Analysis.WellFoundedConstruction
import Mathlib.SetTheory.Ordinal.Basic

/-! The simultaneous well-founded recursion for prescribed admissible rows and
full-power-set charges. The separate enumeration/dual-coding bridge must supply
these inputs before this theorem yields the final Banach-space obstruction. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

theorem exists_transfinite_construction {I : Type} [LinearOrder I] [WellFoundedLT I]
    (μ μtilde : I → AtomicRows) (R Rtilde : I → Set ℕ)
    (ρ σ : I → ℕ → PairedMeasure)
    (hsmall : ∀ a : I, #(Set.Iio a) < 𝔠)
    (hμ : ∀ a, Admissible (μ a)) (hμt : ∀ a, Admissible (μtilde a))
    (hR : ∀ a, (R a).Infinite) (hRt : ∀ a, (Rtilde a).Infinite) :
    ∃ d : ConstructionData μ μtilde R Rtilde,
      GoodConstruction ρ σ d Set.univ ∧ ∀ a, GoodConstruction ρ σ d (Set.Iic a) := by
  classical
  let D : I → Type := fun a => ThreeLevelChoice (μ a) (R a) × ThreeLevelChoice (μtilde a) (Rtilde a)
  let Bbase := stageAlgebra (fun _ : Unit => fun _ : Bool => (∅ : Set ℕ)) ∅
  have hbase : #Bbase < 𝔠 := by
    apply (stageAlgebra_cardinal_le _ _ ℵ₀ le_rfl (by simp)).trans_lt Cardinal.aleph0_lt_continuum
  have hne (a : I) : Nonempty (D a) := by
    obtain ⟨d,_⟩ := exists_threeLevelChoice_nonseparated (R a) (hR a) (μ a) (hμ a) (ρ a)
      Bbase Bbase hbase hbase
    obtain ⟨dt,_⟩ := exists_threeLevelChoice_nonseparated (Rtilde a) (hRt a) (μtilde a) (hμt a) (σ a)
      Bbase Bbase hbase hbase
    exact ⟨(d,dt)⟩
  let fallback : ∀ a, D a := fun a => @Classical.arbitrary (D a) (hne a)
  let P : ∀ a, (∀ b, b < a → D b) → D a → Prop := fun a f x =>
    GoodConstruction ρ σ (historyThrough fallback a f x) (Set.Iic a)
  have hstep (a : I) (f : ∀ b, b < a → D b)
      (ih : ∀ b (hba : b < a), P b (fun c hcb => f c (lt_trans hcb hba)) (f b hba)) :
      ∃ x, P a f x := by
    let past : ConstructionData μ μtilde R Rtilde := fun b => if h : b < a then f b h else fallback b
    have hpast (b : I) (hb : b < a) : past b = f b hb := dif_pos hb
    have hprev (b : Set.Iio a) : GoodConstruction ρ σ past (Set.Iic b.val) := by
      apply (goodConstruction_congr ρ σ
        (historyThrough fallback b.val (fun c hcb => f c (lt_trans hcb b.property)) (f b.val b.property))
        past (Set.Iic b.val) ?_).mp (ih b.val b.property)
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
    have hgood : GoodConstruction ρ σ past (Set.Iio a) := by
      rw [← hcover]
      exact goodConstruction_directed_union ρ σ past _ hdir hprev
    obtain ⟨x,hx⟩ := exists_goodConstruction_insert ρ σ past (Set.Iio a) a
      (lt_irrefl a) (hsmall a) hgood (hR a) (hRt a) (hμ a) (hμt a)
    have hset : insert a (Set.Iio a) = Set.Iic a := by
      ext b
      exact le_iff_eq_or_lt.symm
    refine ⟨x, ?_⟩
    change GoodConstruction ρ σ (Function.update past a x) (Set.Iic a)
    rwa [hset] at hx
  obtain ⟨d,hd⟩ := wellFounded_history_choice wellFounded_lt (fun _ _ _ => lt_trans)
    D hne P hstep
  have hstages (a : I) : GoodConstruction ρ σ d (Set.Iic a) := by
    apply (goodConstruction_congr ρ σ (historyThrough fallback a (fun b _ => d b) (d a))
      d (Set.Iic a) ?_).mp (hd a)
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
  refine ⟨d, ?_, hstages⟩
  rw [← hcover]
  exact goodConstruction_directed_union ρ σ d _ hdir hstages

abbrev ConstructionIndex : Type := (𝔠 : Cardinal.{0}).ord.toType

theorem constructionIndex_cardinal : #ConstructionIndex = 𝔠 := Cardinal.mk_ord_toType _

theorem exists_continuum_construction
    (μ μtilde : ConstructionIndex → AtomicRows) (R Rtilde : ConstructionIndex → Set ℕ)
    (ρ σ : ConstructionIndex → ℕ → PairedMeasure)
    (hμ : ∀ a, Admissible (μ a)) (hμt : ∀ a, Admissible (μtilde a))
    (hR : ∀ a, (R a).Infinite) (hRt : ∀ a, (Rtilde a).Infinite) :
    ∃ d : ConstructionData μ μtilde R Rtilde,
      GoodConstruction ρ σ d Set.univ ∧ ∀ a, GoodConstruction ρ σ d (Set.Iic a) :=
  exists_transfinite_construction μ μtilde R Rtilde ρ σ
    Cardinal.mk_Iio_ord_toType hμ hμt hR hRt

end SigmaNonprimarity
