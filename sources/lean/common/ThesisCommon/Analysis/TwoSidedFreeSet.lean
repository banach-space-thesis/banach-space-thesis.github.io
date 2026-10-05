import ThesisCommon.Analysis.SetMappingDefinitions

/-! Two-sided countable free sets by the manuscript's transfinite recursion.
At each stage in the initial ordinal of |Γ|, avoid all previous choices and
both directed incidence sets. Its forbidden union has cardinality at most
|stage| * aleph-zero, hence strictly below |Γ| even when |Γ| is singular. -/
noncomputable section
open scoped Cardinal
namespace ThesisCommon
universe u
variable {Γ : Type u}

/-- One point and both of its directed incidence sets. -/
def setMappingClosedNeighborhood (F : Γ → Set Γ) (γ : Γ) : Set Γ :=
  insert γ (F γ ∪ {δ | γ ∈ F δ})

theorem setMappingClosedNeighborhood_countable (F : Γ → Set Γ)
    (hF : HasTwoSidedCountableValues F) (γ : Γ) :
    (setMappingClosedNeighborhood F γ).Countable :=
  (hF.1 γ |>.union (hF.2 γ)).insert γ

/-- The exact cardinal bound used for the forbidden set at a recursion stage. -/
theorem mk_iUnion_countable_le {ι : Type u} (A : ι → Set Γ)
    (hA : ∀ i, (A i).Countable) :
    Cardinal.mk (⋃ i, A i) ≤ Cardinal.mk ι * Cardinal.aleph0 := by
  calc
    Cardinal.mk (⋃ i, A i) ≤ Cardinal.sum (fun i => Cardinal.mk (A i)) :=
      Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : ι => Cardinal.aleph0) :=
      Cardinal.sum_le_sum _ _ (fun i => (hA i).le_aleph0)
    _ = Cardinal.mk ι * Cardinal.aleph0 := Cardinal.sum_const' _ _

/-- A union of fewer than |Γ| countable sets cannot exhaust an uncountable Γ.
No cofinality or regularity condition is involved. -/
theorem exists_outside_small_countable_union {ι : Type u}
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ) (hι : Cardinal.mk ι < Cardinal.mk Γ)
    (A : ι → Set Γ) (hA : ∀ i, (A i).Countable) :
    ∃ γ : Γ, γ ∉ ⋃ i, A i := by
  classical
  have hsmall : Cardinal.mk (⋃ i, A i) < Cardinal.mk Γ :=
    (mk_iUnion_countable_le A hA).trans_lt
      ((Cardinal.mul_le_max_of_aleph0_le_right le_rfl).trans_lt (max_lt hι hΓ))
  by_contra hn
  have hu : (⋃ i, A i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro γ
    by_contra hγ
    exact hn ⟨γ, hγ⟩
  rw [hu, Cardinal.mk_univ] at hsmall
  exact (lt_irrefl _ hsmall)

/-- A valid next value for every possible history on an initial segment. -/
theorem exists_twoSidedFreeStep (F : Γ → Set Γ)
    (hF : HasTwoSidedCountableValues F) (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (a : (Cardinal.mk Γ).ord.toType)
    (r : ∀ b : (Cardinal.mk Γ).ord.toType, b < a → Γ) :
    ∃ γ : Γ, ∀ b (hba : b < a),
      γ ≠ r b hba ∧ γ ∉ F (r b hba) ∧ r b hba ∉ F γ := by
  let A : Set.Iio a → Set Γ := fun b => setMappingClosedNeighborhood F (r b.val b.property)
  obtain ⟨γ, hγ⟩ := exists_outside_small_countable_union hΓ
    (Cardinal.mk_Iio_ord_toType a) A
    (fun b => setMappingClosedNeighborhood_countable F hF (r b.val b.property))
  refine ⟨γ, ?_⟩
  intro b hba
  have hb : γ ∉ A ⟨b, hba⟩ := fun hx => hγ (Set.mem_iUnion.mpr ⟨⟨b, hba⟩, hx⟩)
  simpa only [A, setMappingClosedNeighborhood, Set.mem_insert_iff,
    Set.mem_union, Set.mem_setOf_eq, not_or] using hb

/-- The full two-sided countable free-set theorem, with the source recursion
carried out on the initial ordinal of |Γ|. This stronger reusable version does
not require the irrelevant diagonal condition γ ∉ F γ. -/
theorem twoSided_countable_free_set (F : Γ → Set Γ)
    (hF : HasTwoSidedCountableValues F) (hΓ : Cardinal.aleph0 < Cardinal.mk Γ) :
    ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧ IsSetMappingFree F H := by
  classical
  let I := (Cardinal.mk Γ).ord.toType
  let step (a : I) (r : ∀ b : I, b < a → Γ) : Γ :=
    (exists_twoSidedFreeStep F hF hΓ a r).choose
  have hstep (a : I) (r : ∀ b : I, b < a → Γ) :
      ∀ b (hba : b < a),
        step a r ≠ r b hba ∧ step a r ∉ F (r b hba) ∧ r b hba ∉ F (step a r) :=
    (exists_twoSidedFreeStep F hF hΓ a r).choose_spec
  let f : I → Γ := IsWellFounded.fix ((· < ·) : I → I → Prop) step
  have hrec (a : I) : f a = step a (fun b _ => f b) :=
    IsWellFounded.fix_eq ((· < ·) : I → I → Prop) step a
  have hf (a b : I) (hba : b < a) : f a ≠ f b ∧ f a ∉ F (f b) ∧ f b ∉ F (f a) := by
    simpa only [← hrec a] using hstep a (fun b _ => f b) b hba
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hf b a hlt).1 hab.symm
    · exact (hf a b hgt).1 hab
  refine ⟨Set.range f, ?_, ?_⟩
  · rw [Cardinal.mk_range_eq f hinj]
    exact Cardinal.mk_ord_toType _
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
    have hab : a ≠ b := fun h => hne (congrArg f h)
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact ⟨(hf b a hlt).2.2, (hf b a hlt).2.1⟩
    · exact (hf a b hgt).2

end ThesisCommon
