import ThesisCommon.Analysis.HajnalThinning

/-! Construction of the one-way free blocks used by the singular-cardinal
partition proof of Hajnal's free-set theorem. -/
noncomputable section
open scoped Cardinal
namespace ThesisCommon
universe u
variable {Γ : Type u}

/-- Apply the regular case within a subset of the ambient set. -/
theorem hajnal_on_regular_subset (F : Γ → Set Γ) (μ : Cardinal.{u})
    (S : Set Γ) (hS : (Cardinal.mk S).IsRegular) (hμ : μ < Cardinal.mk S)
    (hF : ∀ x, Cardinal.mk (F x) < μ) :
    ∃ H : Set Γ, H ⊆ S ∧ Cardinal.mk H = Cardinal.mk S ∧ IsSetMappingFree F H := by
  classical
  let G (x : S) : Set S := {y | y.val ∈ F x.val}
  have hG (x : S) : Cardinal.mk (G x) < μ := by
    apply lt_of_le_of_lt ?_ (hF x.val)
    apply Cardinal.mk_le_of_injective (f := fun y : G x => (⟨y.val.val, y.property⟩ : F x.val))
    intro y z hyz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : F x.val => w.val) hyz
  obtain ⟨A, hAcard, hAfree⟩ := hajnal_of_isRegular G μ hS hμ hG
  let f : A → Γ := fun x => x.val.val
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext h)
  refine ⟨Set.range f, ?_, (Cardinal.mk_range_eq f hf).trans hAcard, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact x.val.property
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    exact hAfree x.val x.property y.val y.property
      (fun h => hxy (congrArg Subtype.val h))

/-- A subset of cardinality at least a regular κ contains a free subset of
cardinality κ whenever all values of the mapping have a fixed bound below κ. -/
theorem exists_regular_free_subset (F : Γ → Set Γ) (μ κ : Cardinal.{u})
    (hκ : κ.IsRegular) (hμ : μ < κ) (hF : ∀ x, Cardinal.mk (F x) < μ)
    (S : Set Γ) (hsize : κ ≤ Cardinal.mk S) :
    ∃ H : Set Γ, H ⊆ S ∧ Cardinal.mk H = κ ∧ IsSetMappingFree F H := by
  classical
  obtain ⟨A, hA⟩ := Cardinal.le_mk_iff_exists_set.mp hsize
  let f : A → Γ := fun x => x.val.val
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext h)
  have hcard : Cardinal.mk (Set.range f) = κ := (Cardinal.mk_range_eq f hf).trans hA
  obtain ⟨H, hH, hHcard, hHfree⟩ := hajnal_on_regular_subset F μ (Set.range f)
    (by simpa only [hcard] using hκ) (by simpa only [hcard] using hμ) hF
  refine ⟨H, ?_, hHcard.trans hcard, hHfree⟩
  intro x hx
  obtain ⟨y, rfl⟩ := hH hx
  exact y.val.property

/-- Recursively choose regular-sized free blocks outside all previous blocks
and their outgoing images. This yields disjoint blocks without forward edges. -/
theorem exists_oneWay_regular_free_blocks {ι : Type u} [LinearOrder ι]
    [IsWellFounded ι ((· < ·) : ι → ι → Prop)]
    (F : Γ → Set Γ) (μ : Cardinal.{u}) (s : ι → Cardinal.{u})
    (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (hreg : ∀ i, (s i).IsRegular) (hμ : ∀ i, μ < s i)
    (hι : ∀ i, Cardinal.mk ι < s i) (hsΓ : ∀ i, s i ≤ Cardinal.mk Γ)
    (hmono : StrictMono s) (hF : ∀ x, Cardinal.mk (F x) < μ) :
    ∃ B : ι → Set Γ,
      (∀ i, Cardinal.mk (B i) = s i) ∧ (∀ i, IsSetMappingFree F (B i)) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      ∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, y ∉ F x := by
  classical
  haveI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp hΓ
  let C (i : ι) := {S : Set Γ // Cardinal.mk S = s i ∧ IsSetMappingFree F S}
  let P (i : ι) (r : ∀ j : ι, j < i → C j) : Set Γ := ⋃ j : Set.Iio i, (r j.val j.property).val
  let Q (i : ι) (r : ∀ j : ι, j < i → C j) : Set Γ :=
    P i r ∪ ⋃ x : P i r, F x.val
  have hstep (i : ι) (r : ∀ j : ι, j < i → C j) : ∃ b : C i, b.val ⊆ (Q i r)ᶜ := by
    have hP : Cardinal.mk (P i r) < s i := by
      apply mk_iUnion_lt_of_index_lt_cofinality (hreg i).aleph0_le
      · rw [(hreg i).cof_eq]
        exact (Cardinal.mk_subtype_le _).trans_lt (hι i)
      · intro j
        rw [(r j.val j.property).property.1]
        exact hmono j.property
    have hQ : Cardinal.mk (Q i r) < s i :=
      mk_setMapping_union_lt F (hreg i).aleph0_le (hμ i) hF (P i r) hP
    have hcompl : Cardinal.mk ((Q i r)ᶜ : Set Γ) = Cardinal.mk Γ :=
      Cardinal.mk_compl_of_infinite _ (hQ.trans_le (hsΓ i))
    obtain ⟨H, hH, hcard, hfree⟩ := exists_regular_free_subset F μ (s i) (hreg i)
      (hμ i) hF (Q i r)ᶜ (by simpa only [hcompl] using hsΓ i)
    exact ⟨⟨H, hcard, hfree⟩, hH⟩
  let step (i : ι) (r : ∀ j : ι, j < i → C j) : C i := (hstep i r).choose
  let a : ∀ i, C i := IsWellFounded.fix ((· < ·) : ι → ι → Prop) step
  have hrec (i : ι) : a i = step i (fun j _ => a j) :=
    IsWellFounded.fix_eq ((· < ·) : ι → ι → Prop) step i
  have havoid (i : ι) : (a i).val ⊆ (Q i (fun j _ => a j))ᶜ := by
    rw [hrec i]
    exact (hstep i (fun j _ => a j)).choose_spec
  refine ⟨fun i => (a i).val, fun i => (a i).property.1,
    fun i => (a i).property.2, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact havoid j hxj (Or.inl (Set.mem_iUnion.mpr ⟨⟨i, hij⟩, hxi⟩))
    · exact havoid i hxi (Or.inl (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩))
  · intro i j hij x hxi y hyj hyFx
    exact havoid j hyj (Or.inr (Set.mem_iUnion.mpr
      ⟨⟨x, Set.mem_iUnion.mpr ⟨⟨i, hij⟩, hxi⟩⟩, hyFx⟩))

end ThesisCommon
