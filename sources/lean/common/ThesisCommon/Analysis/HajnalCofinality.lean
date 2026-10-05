import ThesisCommon.Analysis.SetMappingMaximal

/-! The cofinality case of Hajnal's free-set theorem.
Following the maximal-free-family proof (Lázár's lemma), recursively remove
maximal free sets for μ stages. A point outside their union and its outgoing
images has to hit every disjoint member, contradicting its value-size bound.
The hypothesis μ < cf(|Γ|) is retained explicitly in this preliminary result. -/
noncomputable section
open scoped Cardinal
namespace ThesisCommon
universe u
variable {Γ : Type u}

theorem mk_iUnion_lt_of_index_lt_cofinality {ι : Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hι : Cardinal.mk ι < κ.ord.cof)
    (A : ι → Set Γ) (hA : ∀ i, Cardinal.mk (A i) < κ) :
    Cardinal.mk (⋃ i, A i) < κ :=
  Cardinal.mk_iUnion_le_sum_mk.trans_lt
    ((Cardinal.sum_le_iSup _).trans_lt
      (Cardinal.mul_lt_of_lt hκ (hι.trans_le (Ordinal.cof_ord_le κ))
        (Ordinal.iSup_lt hι hA)))

theorem mk_setMapping_union_lt (F : Γ → Set Γ) {μ κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hμ : μ < κ)
    (hF : ∀ x, Cardinal.mk (F x) < μ) (S : Set Γ)
    (hS : Cardinal.mk S < κ) :
    Cardinal.mk ((S ∪ ⋃ x : S, F x.val) : Set Γ) < κ := by
  have himage : Cardinal.mk (⋃ x : S, F x.val) ≤ Cardinal.mk S * μ := by
    calc
      _ ≤ Cardinal.sum (fun x : S => Cardinal.mk (F x.val)) :=
        Cardinal.mk_iUnion_le_sum_mk
      _ ≤ Cardinal.sum (fun _ : S => μ) :=
        Cardinal.sum_le_sum _ _ (fun x => (hF x.val).le)
      _ = Cardinal.mk S * μ := Cardinal.sum_const' _ _
  exact (Cardinal.mk_union_le _ _).trans_lt
    (Cardinal.add_lt_of_lt hκ hS (himage.trans_lt (Cardinal.mul_lt_of_lt hκ hS hμ)))

/-- A transfinite family of maximal free sets in successive residual sets.
The family has μ stages, regardless of whether μ is finite or infinite. -/
theorem exists_transfinite_maximalFreeFamily (F : Γ → Set Γ) (μ : Cardinal.{u}) :
    ∃ A : μ.ord.toType → Set Γ, ∀ i,
      Maximal (fun H => H ⊆ (⋃ j : Set.Iio i, A j.val)ᶜ ∧ IsSetMappingFree F H) (A i) := by
  classical
  let I := μ.ord.toType
  let chooseMax (S : Set Γ) : Set Γ := (exists_maximal_setMappingFree F S).choose
  have hchoose (S : Set Γ) : Maximal (fun H => H ⊆ S ∧ IsSetMappingFree F H) (chooseMax S) :=
    (exists_maximal_setMappingFree F S).choose_spec
  let step (i : I) (r : ∀ j : I, j < i → Set Γ) : Set Γ :=
    chooseMax (⋃ j : Set.Iio i, r j.val j.property)ᶜ
  let A : I → Set Γ := IsWellFounded.fix ((· < ·) : I → I → Prop) step
  have hrec (i : I) : A i = chooseMax (⋃ j : Set.Iio i, A j.val)ᶜ :=
    IsWellFounded.fix_eq ((· < ·) : I → I → Prop) step i
  refine ⟨A, fun i => ?_⟩
  simpa only [← hrec i] using hchoose (⋃ j : Set.Iio i, A j.val)ᶜ

/-- Hajnal's preliminary cofinality case, including finite μ and countable Γ.
No regularity is assumed, but the displayed μ < cf(|Γ|) hypothesis is essential
to this preliminary proof and is not being claimed for the full theorem. -/
theorem hajnal_of_lt_cofinality (F : Γ → Set Γ) (μ : Cardinal.{u})
    (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (hμ : μ < (Cardinal.mk Γ).ord.cof)
    (hF : ∀ x, Cardinal.mk (F x) < μ) :
    ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧ IsSetMappingFree F H := by
  classical
  by_contra hnone
  have hsmall (H : Set Γ) (hH : IsSetMappingFree F H) : Cardinal.mk H < Cardinal.mk Γ := by
    have hle : Cardinal.mk H ≤ Cardinal.mk Γ := Cardinal.mk_le_of_injective Subtype.val_injective
    exact (lt_or_eq_of_le hle).resolve_right (fun heq => hnone ⟨H, heq, hH⟩)
  obtain ⟨A, hA⟩ := exists_transfinite_maximalFreeFamily F μ
  have hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (hA j).prop.1 hxj (Set.mem_iUnion.mpr ⟨⟨i, hlt⟩, hxi⟩)
    · exact (hA i).prop.1 hxi (Set.mem_iUnion.mpr ⟨⟨j, hgt⟩, hxj⟩)
  let S : Set Γ := ⋃ i, A i
  have hS : Cardinal.mk S < Cardinal.mk Γ :=
    mk_iUnion_lt_of_index_lt_cofinality hΓ
      (by simpa only [Cardinal.mk_ord_toType] using hμ) A
      (fun i => hsmall (A i) (hA i).prop.2)
  have hbig : Cardinal.mk ((S ∪ ⋃ x : S, F x.val) : Set Γ) < Cardinal.mk Γ :=
    mk_setMapping_union_lt F hΓ (hμ.trans_le (Ordinal.cof_ord_le _)) hF S hS
  obtain ⟨x, hx⟩ := Cardinal.compl_nonempty_of_mk_lt_mk hbig
  have hxS : x ∉ S := fun h => hx (Or.inl h)
  have hout (y : Γ) (hy : y ∈ S) : x ∉ F y :=
    fun h => hx (Or.inr (Set.mem_iUnion.mpr ⟨⟨y, hy⟩, h⟩))
  have hhits (i : μ.ord.toType) : ∃ y ∈ A i, y ∈ F x := by
    apply maximal_setMappingFree_hits (hA i)
    · rintro ⟨_, ⟨j, rfl⟩, h⟩
      exact hxS (Set.mem_iUnion.mpr ⟨j.val, h⟩)
    · exact fun h => hxS (Set.mem_iUnion.mpr ⟨i, h⟩)
    · intro y hy
      exact hout y (Set.mem_iUnion.mpr ⟨i, hy⟩)
  choose y hyA hyF using hhits
  have hyinj : Function.Injective y := by
    intro i j heq
    by_contra hne
    apply Set.disjoint_left.mp (hdisjoint hne) (hyA i)
    rw [heq]
    exact hyA j
  have hcard : Cardinal.mk μ.ord.toType ≤ Cardinal.mk (F x) :=
    Cardinal.mk_le_of_injective (f := fun i => (⟨y i, hyF i⟩ : F x))
      (fun _ _ h => hyinj (congrArg Subtype.val h))
  rw [Cardinal.mk_ord_toType] at hcard
  exact (hF x).not_ge hcard

/-- In particular all regular-cardinal instances of the full target are proved. -/
theorem hajnal_of_isRegular (F : Γ → Set Γ) (μ : Cardinal.{u})
    (hΓ : (Cardinal.mk Γ).IsRegular) (hμ : μ < Cardinal.mk Γ)
    (hF : ∀ x, Cardinal.mk (F x) < μ) :
    ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧ IsSetMappingFree F H :=
  hajnal_of_lt_cofinality F μ hΓ.aleph0_le (by simpa only [hΓ.cof_eq] using hμ) hF

end ThesisCommon
