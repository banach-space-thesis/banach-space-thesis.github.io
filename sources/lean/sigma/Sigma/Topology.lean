import Sigma.Compacta

/-! The locally compact Hausdorff almost-disjoint space and its compactification. -/
noncomputable section
open Set Topology
namespace SigmaNonprimarity

@[simp] theorem inr_mem_tail (B : Set (Set Point)) (b c : B) (F : Finset Point) :
    Sum.inr c ∈ tailNeighborhood B b F ↔ c = b := by
  change (Sum.inr c = Sum.inr b ∨
    ∃ x ∈ b.val, x ∉ F ∧ Sum.inr c = Sum.inl x) ↔ c = b
  simp

@[simp] theorem inl_mem_tail (B : Set (Set Point)) (b : B) (F : Finset Point) (x : Point) :
    Sum.inl x ∈ tailNeighborhood B b F ↔ x ∈ b.val ∧ x ∉ F := by
  change (Sum.inl x = Sum.inr b ∨
    ∃ y ∈ b.val, y ∉ F ∧ Sum.inl x = Sum.inl y) ↔ x ∈ b.val ∧ x ∉ F
  simp only [reduceCtorEq, false_or, Sum.inl.injEq]
  constructor
  · rintro ⟨y, hy, hyF, rfl⟩
    exact ⟨hy, hyF⟩
  · rintro ⟨hx, hxF⟩
    exact ⟨x, hx, hxF, rfl⟩

theorem isOpen_base_singleton (B : Set (Set Point)) (p : Point) :
    IsOpen ({Sum.inl p} : Set (MrowkaBase B)) :=
  TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl ⟨p, rfl⟩)

theorem isOpen_tail (B : Set (Set Point)) (b : B) (F : Finset Point) :
    IsOpen (tailNeighborhood B b F) :=
  TopologicalSpace.isOpen_generateFrom_of_mem (Or.inr ⟨b, F, rfl⟩)

theorem tail_subset_of_isOpen {B : Set (Set Point)} {U : Set (MrowkaBase B)}
    (hU : IsOpen U) (b : B) (hb : Sum.inr b ∈ U) :
    ∃ F : Finset Point, tailNeighborhood B b F ⊆ U := by
  classical
  induction hU with
  | basic U hU =>
    rcases hU with ⟨p, rfl⟩ | ⟨c, F, rfl⟩
    · cases hb
    · have hbc : b = c := (inr_mem_tail B c b F).mp hb
      subst c
      exact ⟨F, Subset.rfl⟩
  | univ => exact ⟨∅, subset_univ _⟩
  | inter U V _ _ ihU ihV =>
    obtain ⟨F, hF⟩ := ihU hb.1
    obtain ⟨G, hG⟩ := ihV hb.2
    refine ⟨F ∪ G, fun p hp => ⟨hF ?_, hG ?_⟩⟩
    · rcases p with x | c
      · simp only [inl_mem_tail, Finset.mem_union, not_or] at hp ⊢
        exact ⟨hp.1, hp.2.1⟩
      · simpa only [inr_mem_tail] using hp
    · rcases p with x | c
      · simp only [inl_mem_tail, Finset.mem_union, not_or] at hp ⊢
        exact ⟨hp.1, hp.2.2⟩
      · simpa only [inr_mem_tail] using hp
  | sUnion S _ ih =>
    obtain ⟨U, hUS, hbU⟩ := hb
    obtain ⟨F, hF⟩ := ih U hUS hbU
    exact ⟨F, hF.trans (subset_sUnion_of_mem hUS)⟩

theorem isCompact_tail (B : Set (Set Point)) (b : B) (F : Finset Point) :
    IsCompact (tailNeighborhood B b F) := by
  classical
  apply isCompact_iff_finite_subcover.mpr
  intro ι U hU hcover
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ((inr_mem_tail B b b F).mpr rfl))
  obtain ⟨G, hG⟩ := tail_subset_of_isOpen (hU i) b hi
  let R : Set (MrowkaBase B) := tailNeighborhood B b F \ U i
  have hR : R.Finite := by
    apply ((G.finite_toSet).image (fun p : Point => (Sum.inl p : MrowkaBase B))).subset
    intro p hp
    rcases p with x | c
    · have hxG : x ∈ G := by
        by_contra hn
        exact hp.2 (hG ((inl_mem_tail B b G x).mpr
          ⟨((inl_mem_tail B b F x).mp hp.1).1, hn⟩))
      exact ⟨x, hxG, rfl⟩
    · have hc := (inr_mem_tail B b c F).mp hp.1
      subst c
      exact False.elim (hp.2 hi)
  obtain ⟨t, ht⟩ := hR.isCompact.elim_finite_subcover U hU (fun p hp => hcover hp.1)
  refine ⟨insert i t, fun p hp => ?_⟩
  by_cases hpi : p ∈ U i
  · exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, hpi⟩⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.mp (ht ⟨hp, hpi⟩)
    obtain ⟨hjt, hpj⟩ := mem_iUnion.mp hj
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hjt, hpj⟩⟩

instance mrowkaLocallyCompact (B : Set (Set Point)) : LocallyCompactSpace (MrowkaBase B) where
  local_compact_nhds p U hU := by
    obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp hU
    rcases p with x | b
    · exact ⟨{Sum.inl x}, (isOpen_base_singleton B x).mem_nhds rfl,
        (singleton_subset_iff.mpr hpV).trans hVU, isCompact_singleton⟩
    · obtain ⟨F, hF⟩ := tail_subset_of_isOpen hV b hpV
      exact ⟨tailNeighborhood B b F, (isOpen_tail B b F).mem_nhds (by simp),
        hF.trans hVU, isCompact_tail B b F⟩

theorem mrowkaT2 {B : Set (Set Point)} (hB : AlmostDisjoint B) : T2Space (MrowkaBase B) where
  t2 p q hpq := by
    classical
    rcases p with x | b <;> rcases q with y | c
    · exact ⟨{Sum.inl x}, {Sum.inl y}, isOpen_base_singleton B x,
        isOpen_base_singleton B y, rfl, rfl, disjoint_singleton.mpr hpq⟩
    · refine ⟨{Sum.inl x}, tailNeighborhood B c {x}, isOpen_base_singleton B x,
        isOpen_tail B c {x}, rfl, by simp, ?_⟩
      simp
    · refine ⟨tailNeighborhood B b {y}, {Sum.inl y}, isOpen_tail B b {y},
        isOpen_base_singleton B y, by simp, rfl, ?_⟩
      simp
    · have hbc : b.val ≠ c.val := fun h => hpq (congrArg Sum.inr (Subtype.ext h))
      have hfin := hB.2 b.val b.property c.val c.property hbc
      refine ⟨tailNeighborhood B b hfin.toFinset, tailNeighborhood B c ∅,
        isOpen_tail B b _, isOpen_tail B c _, by simp, by simp, ?_⟩
      apply Set.disjoint_left.mpr
      intro p hpb hpc
      rcases p with x | d
      · have hxb := (inl_mem_tail B b _ x).mp hpb
        have hxc := (inl_mem_tail B c _ x).mp hpc
        exact hxb.2 (hfin.mem_toFinset.mpr ⟨hxb.1, hxc.1⟩)
      · have hdb := (inr_mem_tail B b d _).mp hpb
        have hdc := (inr_mem_tail B c d _).mp hpc
        exact hpq (congrArg Sum.inr (hdb.symm.trans hdc))

theorem compactumProperties (B : Set (Set Point)) : CompactumProperties B := by
  intro hB
  letI := mrowkaT2 hB
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem baseDense {B : Set (Set Point)} (hB : AlmostDisjoint B) :
    DenseRange (Sum.inl : Point → MrowkaBase B) := by
  intro p
  rcases p with x | b
  · exact subset_closure ⟨x, rfl⟩
  · apply mem_closure_iff.mpr
    intro U hU hbU
    obtain ⟨F, hF⟩ := tail_subset_of_isOpen hU b hbU
    obtain ⟨x, hxb, hxF⟩ := (hB.1 b.val b.property).exists_notMem_finset F
    exact ⟨Sum.inl x, hF ((inl_mem_tail B b F x).mpr ⟨hxb, hxF⟩), x, rfl⟩

/-- An infinite family of limit points prevents compactness before infinity is added. -/
theorem mrowkaNoncompact {B : Set (Set Point)} (hB : B.Infinite) :
    NoncompactSpace (MrowkaBase B) where
  noncompact_univ hc := by
    classical
    let U : MrowkaBase B → Set (MrowkaBase B) :=
      Sum.elim (fun x => {Sum.inl x}) (fun b => tailNeighborhood B b ∅)
    have hU (p) : IsOpen (U p) := by
      rcases p with x | b
      · exact isOpen_base_singleton B x
      · exact isOpen_tail B b ∅
    have hcover : Set.univ ⊆ ⋃ p, U p := by
      intro p _
      apply mem_iUnion.mpr
      refine ⟨p, ?_⟩
      rcases p with x | b
      · rfl
      · exact (inr_mem_tail B b b ∅).mpr rfl
    obtain ⟨t, ht⟩ := hc.elim_finite_subcover U hU hcover
    have hall : Set.univ ⊆ (Sum.inr : B → MrowkaBase B) ⁻¹' (↑t : Set (MrowkaBase B)) := by
      intro b _
      obtain ⟨p, hp⟩ := mem_iUnion.mp (ht (mem_univ (Sum.inr b)))
      obtain ⟨hpt, hbp⟩ := mem_iUnion.mp hp
      rcases p with x | c
      · cases hbp
      · have hbc : b = c := (inr_mem_tail B c b ∅).mp hbp
        subst c
        exact hpt
    have hf : (Set.univ : Set B).Finite :=
      (t.finite_toSet.preimage Sum.inr_injective.injOn).subset hall
    exact hB (Set.finite_coe_iff.mp (Set.finite_univ_iff.mp hf))

/-- Density in K_B requires an infinite family; the extra point is kept explicitly. -/
theorem compactumBaseDense {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    DenseRange (fun p : Point => (↑(Sum.inl p : MrowkaBase B) : AUCompactum B)) := by
  letI := mrowkaNoncompact hInf
  exact OnePoint.denseRange_coe.comp (baseDense hB) OnePoint.continuous_coe

end SigmaNonprimarity
