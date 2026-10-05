import ThesisCommon.Analysis.HajnalPartitionTools

/-! The partition-and-tail thinning argument in the singular case of Hajnal's
theorem. The input blocks have regular cardinalities; their union need not.
This module deliberately states its block hypotheses explicitly. -/
noncomputable section
open scoped Cardinal
namespace ThesisCommon
universe u
variable {Γ : Type u}

/-- A row of disjoint, full-cardinality pieces, with a selected tail threshold. -/
structure HajnalPartitionRow (B : Set Γ) (ν : Cardinal.{u}) where
  pieces : ν.ord.toType → Set Γ
  subset : ∀ p, pieces p ⊆ B
  disjoint : Pairwise (fun p q => Disjoint (pieces p) (pieces q))
  card : ∀ p, Cardinal.mk (pieces p) = Cardinal.mk B
  threshold : ν.ord.toType

theorem exists_hajnal_partitionRow {ι : Type u} [LinearOrder ι]
    (F : Γ → Set Γ) (ν : Cardinal.{u}) (hν : ν.IsRegular)
    (B : ι → Set Γ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hreg : ∀ i, (Cardinal.mk (B i)).IsRegular)
    (hlarge : ∀ i, ν < Cardinal.mk (B i))
    (hF : ∀ x, Cardinal.mk (F x) < ν)
    (i : ι) (r : ∀ j : ι, j < i → HajnalPartitionRow (B j) ν) :
    ∃ row : HajnalPartitionRow (B i) ν,
      ∀ p x, x ∈ row.pieces p → ∀ j (hj : j < i),
        ∀ q, row.threshold ≤ q → Disjoint (F x) ((r j hj).pieces q) := by
  classical
  let E (p : ν.ord.toType) : Set Γ := ⋃ j : Set.Iio i, (r j.val j.property).pieces p
  have hE : Pairwise (fun p q => Disjoint (E p) (E q)) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro x hxp hxq
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxp
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxq
    by_cases hjk : j = k
    · subst k
      exact Set.disjoint_left.mp ((r j.val j.property).disjoint hpq) hxj hxk
    · exact Set.disjoint_left.mp (hB (fun h => hjk (Subtype.ext h)))
        ((r j.val j.property).subset p hxj) ((r k.val k.property).subset q hxk)
  have htail (x : B i) : ∃ p : ν.ord.toType, ∀ q, p ≤ q → Disjoint (F x.val) (E q) :=
    exists_disjoint_tail ν hν E hE (F x.val) (hF x.val)
  choose t ht using htail
  obtain ⟨p, D, hD, hcard, hconst⟩ := exists_fullCardinality_constant_subset
    (B i) (hreg i) (by simpa only [Cardinal.mk_ord_toType] using hlarge i) t
  obtain ⟨A, hA, hAdisj, hAcard, _⟩ := exists_fullCardinality_partition D ν
    (by simpa only [hcard] using (hreg i).aleph0_le)
    ((Cardinal.aleph0_pos).trans_le hν.aleph0_le)
    (by simpa only [hcard] using (hlarge i).le)
  refine ⟨⟨A, fun q => (hA q).trans hD, hAdisj,
    fun q => (hAcard q).trans hcard, p⟩, ?_⟩
  intro q x hx j hj s hps
  apply (ht ⟨x, hD (hA q hx)⟩ s ?_).mono_right
    (Set.subset_iUnion_of_subset ⟨j, hj⟩ (by rfl))
  simpa only [hconst x (hA q hx)] using hps

/-- Thin a well-ordered family of regular-sized free blocks to a free set
whose cardinality dominates every input block. Earlier blocks already have
no outgoing edges to later blocks; the tail argument removes reverse edges. -/
theorem hajnal_thin_regular_blocks {ι : Type u} [LinearOrder ι]
    [IsWellFounded ι ((· < ·) : ι → ι → Prop)]
    (F : Γ → Set Γ) (ν : Cardinal.{u}) (hν : ν.IsRegular)
    (hι : Cardinal.mk ι < ν) (B : ι → Set Γ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hreg : ∀ i, (Cardinal.mk (B i)).IsRegular)
    (hlarge : ∀ i, ν < Cardinal.mk (B i))
    (hfree : ∀ i, IsSetMappingFree F (B i))
    (hforward : ∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, y ∉ F x)
    (hF : ∀ x, Cardinal.mk (F x) < ν) :
    ∃ H : Set Γ, IsSetMappingFree F H ∧ ∀ i, Cardinal.mk (B i) ≤ Cardinal.mk H := by
  classical
  let step (i : ι) (r : ∀ j : ι, j < i → HajnalPartitionRow (B j) ν) :
      HajnalPartitionRow (B i) ν :=
    (exists_hajnal_partitionRow F ν hν B hB hreg hlarge hF i r).choose
  let row : ∀ i, HajnalPartitionRow (B i) ν :=
    IsWellFounded.fix ((· < ·) : ι → ι → Prop) step
  have hrec (i : ι) : row i = step i (fun j _ => row j) :=
    IsWellFounded.fix_eq ((· < ·) : ι → ι → Prop) step i
  have hcross (i : ι) : ∀ p x, x ∈ (row i).pieces p → ∀ j (hj : j < i),
      ∀ q, (row i).threshold ≤ q → Disjoint (F x) ((row j).pieces q) := by
    have h := (exists_hajnal_partitionRow F ν hν B hB hreg hlarge hF i
      (fun j _ => row j)).choose_spec
    change ∀ p x, x ∈ (step i (fun j _ => row j)).pieces p → ∀ j (hj : j < i),
      ∀ q, (step i (fun j _ => row j)).threshold ≤ q →
        Disjoint (F x) ((row j).pieces q) at h
    simpa only [← hrec i] using h
  let T : Set ν.ord.toType := Set.range (fun i => (row i).threshold)
  have hT : Cardinal.mk T < (Ordinal.type ((· < ·) : ν.ord.toType → _ → Prop)).cof := by
    rw [Ordinal.type_toType, hν.cof_eq]
    exact Cardinal.mk_range_le.trans_lt hι
  obtain ⟨p, hp⟩ := Ordinal.lt_cof_type
    (r := ((· < ·) : ν.ord.toType → _ → Prop)) hT
  have htail (i : ι) : (row i).threshold ≤ p := (hp _ (Set.mem_range_self i)).le
  let H : Set Γ := ⋃ i, (row i).pieces p
  refine ⟨H, ?_, fun i => ?_⟩
  · intro x hx y hy hxy
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
    rcases lt_trichotomy i j with hij | hij | hij
    · refine ⟨?_, hforward i j hij x ((row i).subset p hxi) y ((row j).subset p hyj)⟩
      exact fun h => Set.disjoint_left.mp (hcross j p y hyj i hij p (htail j)) h hxi
    · subst j
      exact hfree i x ((row i).subset p hxi) y ((row i).subset p hyj) hxy
    · refine ⟨hforward j i hij y ((row j).subset p hyj) x ((row i).subset p hxi), ?_⟩
      exact fun h => Set.disjoint_left.mp (hcross i p x hxi j hij p (htail i)) h hyj
  · rw [← (row i).card p]
    exact Cardinal.mk_le_mk_of_subset (Set.subset_iUnion (fun i => (row i).pieces p) i)

end ThesisCommon
