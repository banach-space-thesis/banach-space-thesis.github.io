import ThesisCommon.Analysis.SetMappingDefinitions
import Mathlib.Order.WellFounded

/-! The first-unused-point construction of a triangular countable partition.
Each block is obtained by countably many outgoing-closure steps outside the
previous blocks. Empty blocks after exhaustion handle small index sets too. -/
noncomputable section
namespace ThesisCommon
universe u
variable {Γ : Type u}

theorem exists_countableClosure_avoiding (F : Γ → Set Γ)
    (hF : ∀ x, (F x).Countable) (P : Set Γ) (x : Γ) (hx : x ∉ P) :
    ∃ B : Set Γ, B.Countable ∧ x ∈ B ∧ B ⊆ Pᶜ ∧
      ∀ y ∈ B, F y ⊆ P ∪ B := by
  classical
  let C : ℕ → Set Γ := Nat.rec {x} (fun _ S => S ∪ ((⋃ y ∈ S, F y) \ P))
  have hC (n : ℕ) : (C n).Countable ∧ C n ⊆ Pᶜ := by
    induction n with
    | zero => exact ⟨Set.countable_singleton x, fun y hy => by simpa only [Set.mem_singleton_iff.mp hy] using hx⟩
    | succ n ih =>
      refine ⟨ih.1.union ((ih.1.biUnion (fun y _ => hF y)).mono Set.diff_subset), ?_⟩
      intro y hy
      rcases hy with hy | hy
      · exact ih.2 hy
      · exact hy.2
  refine ⟨⋃ n, C n, Set.countable_iUnion (fun n => (hC n).1),
    Set.mem_iUnion.mpr ⟨0, Set.mem_singleton x⟩, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    exact (hC n).2 hn
  · intro y hy z hz
    by_cases hzP : z ∈ P
    · exact Or.inl hzP
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      exact Or.inr (Set.mem_iUnion.mpr ⟨n + 1,
        Or.inr ⟨Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hn, hz⟩⟩, hzP⟩⟩)

theorem exists_countableTriangularBlock (F : Γ → Set Γ)
    (hF : ∀ x, (F x).Countable) (e : (Cardinal.mk Γ).ord.toType ≃ Γ) (P : Set Γ) :
    ∃ B : Set Γ, B.Countable ∧ B ⊆ Pᶜ ∧
      (∀ y ∈ B, F y ⊆ P ∪ B) ∧
      ∀ x ∉ P, ∃ y ∈ B, e.symm y ≤ e.symm x := by
  classical
  let U : Set (Cardinal.mk Γ).ord.toType := {i | e i ∉ P}
  by_cases hU : U.Nonempty
  · let i := wellFounded_lt.min U hU
    have hi : e i ∉ P := wellFounded_lt.min_mem U hU
    obtain ⟨B, hB, hiB, hBP, hBF⟩ := exists_countableClosure_avoiding F hF P (e i) hi
    refine ⟨B, hB, hBP, hBF, ?_⟩
    intro x hx
    refine ⟨e i, hiB, ?_⟩
    simpa only [e.symm_apply_apply] using
      (wellFounded_lt.min_le (show e.symm x ∈ U by simpa only [U, Set.mem_setOf_eq, e.apply_symm_apply] using hx) hU)
  · refine ⟨∅, Set.countable_empty, Set.empty_subset _, ?_, ?_⟩
    · intro y hy
      exact hy.elim
    · intro x hx
      exact (hU ⟨e.symm x, by simpa only [U, Set.mem_setOf_eq, e.apply_symm_apply] using hx⟩).elim

/-- The partition follows the source's first-unused-point recursion.
Every image of a point in block α lies in a block at most α. -/
theorem countable_triangular_partition (F : Γ → Set Γ)
    (hF : ∀ x, (F x).Countable) :
    ∃ B : (Cardinal.mk Γ).ord.toType → Set Γ,
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i, (B i).Countable) ∧ (⋃ i, B i) = Set.univ ∧
      ∀ i x, x ∈ B i → F x ⊆ ⋃ j ≤ i, B j := by
  classical
  let I := (Cardinal.mk Γ).ord.toType
  obtain ⟨e⟩ := Cardinal.eq.mp (Cardinal.mk_ord_toType (Cardinal.mk Γ))
  let chooseBlock (P : Set Γ) : Set Γ := (exists_countableTriangularBlock F hF e P).choose
  have hchoose (P : Set Γ) : (chooseBlock P).Countable ∧ chooseBlock P ⊆ Pᶜ ∧
      (∀ y ∈ chooseBlock P, F y ⊆ P ∪ chooseBlock P) ∧
      ∀ x ∉ P, ∃ y ∈ chooseBlock P, e.symm y ≤ e.symm x :=
    (exists_countableTriangularBlock F hF e P).choose_spec
  let step (i : I) (r : ∀ j : I, j < i → Set Γ) : Set Γ :=
    chooseBlock (⋃ j : Set.Iio i, r j.val j.property)
  let B : I → Set Γ := IsWellFounded.fix ((· < ·) : I → I → Prop) step
  have hrec (i : I) : B i = chooseBlock (⋃ j : Set.Iio i, B j.val) :=
    IsWellFounded.fix_eq ((· < ·) : I → I → Prop) step i
  have hspec (i : I) : (B i).Countable ∧ B i ⊆ (⋃ j : Set.Iio i, B j.val)ᶜ ∧
      (∀ y ∈ B i, F y ⊆ (⋃ j : Set.Iio i, B j.val) ∪ B i) ∧
      ∀ x ∉ ⋃ j : Set.Iio i, B j.val, ∃ y ∈ B i, e.symm y ≤ e.symm x := by
    simpa only [← hrec i] using hchoose (⋃ j : Set.Iio i, B j.val)
  have hdisj : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (hspec j).2.1 hxj (Set.mem_iUnion.mpr ⟨⟨i, hij⟩, hxi⟩)
    · exact (hspec i).2.1 hxi (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩)
  have hcover : (⋃ i, B i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hpre (i : I) : x ∉ ⋃ j : Set.Iio i, B j.val := by
      intro h
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      exact hx (Set.mem_iUnion.mpr ⟨j.val, hj⟩)
    choose y hyB hyle using fun i => (hspec i).2.2.2 x (hpre i)
    have hylt (i : I) : e.symm (y i) < e.symm x := by
      refine lt_of_le_of_ne (hyle i) ?_
      intro heq
      have hyx : y i = x := e.symm.injective heq
      exact hx (Set.mem_iUnion.mpr ⟨i, hyx ▸ hyB i⟩)
    have hyinj : Function.Injective y := by
      intro i j hij
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hne) (hyB i) (hij ▸ hyB j)
    have hcard : Cardinal.mk I ≤ Cardinal.mk (Set.Iio (e.symm x)) :=
      Cardinal.mk_le_of_injective (f := fun i => (⟨e.symm (y i), hylt i⟩ : Set.Iio (e.symm x)))
        (fun _ _ h => hyinj (e.symm.injective (congrArg Subtype.val h)))
    rw [Cardinal.mk_ord_toType] at hcard
    exact (Cardinal.mk_Iio_ord_toType (e.symm x)).not_ge hcard
  refine ⟨B, hdisj, fun i => (hspec i).1, hcover, ?_⟩
  intro i x hx z hz
  rcases (hspec i).2.2.1 x hx hz with hz | hz
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨j.val, Set.mem_iUnion.mpr ⟨j.property.le, hj⟩⟩
  · exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨le_rfl, hz⟩⟩

end ThesisCommon
