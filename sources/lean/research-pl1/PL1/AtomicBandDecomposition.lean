import PL1.LatticeAtoms
import PL1.UnconditionalRNP
import BanLat.Substructures.Band.PPP

/-!
# Atomic band projections in Schur Banach lattices

All projections in this module use the given BanLat order and norm. Atomicity
is a stated hypothesis, not a consequence supplied by the imported library.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
universe u v

namespace PL1.AtomicBandDecomposition

variable {E : Type u} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- Every band projection is contractive for the original lattice norm. -/
theorem norm_bandProjection_le (B : ProjectionBand E) (x : E) :
    ‖B.bandProjection x‖ ≤ ‖x‖ := by
  apply norm_le_norm_of_abs_le_abs
  exact (Positive.abs_le_map_abs (Positive.zero_le_iff.mp B.bandProjection_nonneg) x).trans
    (Positive.le_iff.mp B.bandProjection_le_id _ (abs_nonneg x))

/-- The actual continuous linear operator associated with a projection band. -/
def projection (B : ProjectionBand E) : E →L[ℝ] E :=
  B.bandProjection.mkContinuous 1 (fun x => by
    simpa only [one_mul] using norm_bandProjection_le B x)

@[simp] theorem projection_apply (B : ProjectionBand E) (x : E) :
    projection B x = B.bandProjection x := rfl

theorem norm_projection_le (B : ProjectionBand E) : ‖projection B‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa only [one_mul, projection_apply] using norm_bandProjection_le B x)

theorem projection_nonneg (B : ProjectionBand E) {x : E} (hx : 0 ≤ x) :
    0 ≤ projection B x := Positive.zero_le_iff.mp B.bandProjection_nonneg x hx

theorem projection_le_self (B : ProjectionBand E) {x : E} (hx : 0 ≤ x) :
    projection B x ≤ x := Positive.le_iff.mp B.bandProjection_le_id x hx

theorem projection_mem (B : ProjectionBand E) (x : E) : projection B x ∈ B :=
  B.bandProjection_mem x

theorem projection_eq_self (B : ProjectionBand E) {x : E} (hx : x ∈ B) :
    projection B x = x := B.bandProjection_eq_of_mem hx

theorem projection_eq_zero (B : ProjectionBand E) {x : E}
    (hx : x ∈ disjointComplement (B : Set E)) : projection B x = 0 :=
  B.bandProjection_eq_zero_of_mem_dc hx

@[simp] theorem projection_bot : projection (⊥ : ProjectionBand E) = 0 := by
  ext x
  exact ProjectionBand.mem_bot.mp (projection_mem ⊥ x)

theorem projection_comp (B C : ProjectionBand E) :
    (projection B).comp (projection C) = projection (B ⊓ C) := by
  ext x
  exact (LinearMap.congr_fun (ProjectionBand.bandProjection_inf B C) x).symm

theorem projection_comp_of_le {B C : ProjectionBand E} (hBC : B ≤ C) :
    (projection B).comp (projection C) = projection B := by
  rw [projection_comp, inf_eq_left.mpr hBC]

theorem projection_mono {B C : ProjectionBand E} (hBC : B ≤ C)
    {x : E} (hx : 0 ≤ x) : projection B x ≤ projection C x := by
  have h := (ProjectionBand.isLUB_inter_Icc_bandProjection C hx).1
    ⟨hBC (projection_mem B x), projection_nonneg B hx, projection_le_self B hx⟩
  exact h

theorem range_projection (B : ProjectionBand E) :
    (projection B).range = B.toBand.toSubmodule := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact projection_mem B y
  · intro hx
    exact ⟨x, projection_eq_self B hx⟩

/-- A positive element of the principal band of an atom lies on its ray.
The proof uses norm convergence of its actual truncated principal-ideal net. -/
theorem mem_span_of_mem_atom_band_nonneg [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) {a x : E} (ha : IsLatticeAtom a)
    (hx : 0 ≤ x) (hxa : x ∈ Band.generated ({a} : Set E)) :
    x ∈ Submodule.span ℝ ({a} : Set E) := by
  let y : ℕ → E := fun n => x ⊓ (n : ℝ) • a
  have hy : ∀ n, 0 ≤ y n := fun n =>
    le_inf hx (smul_nonneg (Nat.cast_nonneg _) ha.nonneg)
  have hmono : Monotone y := by
    intro m n hmn
    exact inf_le_inf_left _ (smul_le_smul_of_nonneg_right (Nat.cast_le.mpr hmn) ha.nonneg)
  obtain ⟨z, hz⟩ := SchurLattice.exists_tendsto_of_monotone_norm_bounded hS y hmono ‖x‖
    (fun n => norm_le_norm_of_abs_le_abs (by
      rw [abs_of_nonneg (hy n), abs_of_nonneg hx]
      exact inf_le_left))
  have hlub : IsLUB (Set.range y) x := by
    simpa only [y, Nat.cast_smul_eq_nsmul] using
      (Band.mem_generated_singleton_iff_isLUB_inf_nsmul ha.nonneg hx).mp hxa
  have hzx : z = x := (isLUB_of_tendsto_atTop hmono hz).unique hlub
  have hclosed := (Submodule.span ℝ ({a} : Set E)).closed_of_finiteDimensional
  apply hclosed.mem_of_tendsto (hz.trans (by rw [hzx]))
  exact Filter.Eventually.of_forall (fun n => by
    obtain ⟨t, _, ht⟩ := ha.eq_smul_of_nonneg_le_smul (hy n)
      (Nat.cast_nonneg n) (show y n ≤ (n : ℝ) • a from inf_le_right)
    rw [ht]
    exact Submodule.smul_mem _ t (Submodule.subset_span (Set.mem_singleton a)))

/-- The principal band of an atom is exactly its one-dimensional real span. -/
theorem atom_band_eq_span [CompleteSpace E] (hS : HasSchurProperty ℝ E)
    {a : E} (ha : IsLatticeAtom a) :
    (Band.generated ({a} : Set E)).toSubmodule = Submodule.span ℝ ({a} : Set E) := by
  apply le_antisymm
  · intro x hx
    have hp := mem_span_of_mem_atom_band_nonneg hS ha (posPart_nonneg x)
      ((Band.generated ({a} : Set E)).toOrderIdeal.posPart_mem hx)
    have hn := mem_span_of_mem_atom_band_nonneg hS ha (negPart_nonneg x)
      ((Band.generated ({a} : Set E)).toOrderIdeal.negPart_mem hx)
    simpa only [posPart_sub_negPart] using (Submodule.span ℝ ({a} : Set E)).sub_mem hp hn
  · apply Submodule.span_le.mpr
    intro x hx
    exact Band.subset_generated _ hx

/-- Dedekind completeness supplies the projection onto any actual band. -/
def bandOfSchur [CompleteSpace E] (hS : HasSchurProperty ℝ E) (B : Band E) :
    ProjectionBand E :=
  Classical.choose ((ProjectionBand.projectionBand_iff_isLUB_inter_Icc B).mpr (by
    intro x hx
    exact SchurLattice.exists_isLUB hS _
      ⟨0, B.toSubmodule.zero_mem, le_rfl, hx⟩ ⟨x, fun _ hy => hy.2.2⟩))

theorem bandOfSchur_coe [CompleteSpace E] (hS : HasSchurProperty ℝ E) (B : Band E) :
    (bandOfSchur hS B : Set E) = (B : Set E) :=
  Classical.choose_spec ((ProjectionBand.projectionBand_iff_isLUB_inter_Icc B).mpr (by
    intro x hx
    exact SchurLattice.exists_isLUB hS _
      ⟨0, B.toSubmodule.zero_mem, le_rfl, hx⟩ ⟨x, fun _ hy => hy.2.2⟩))

def principalBand [CompleteSpace E] (hS : HasSchurProperty ℝ E) (a : E) :
    ProjectionBand E := bandOfSchur hS (Band.generated ({a} : Set E))

theorem principalBand_coe [CompleteSpace E] (hS : HasSchurProperty ℝ E) (a : E) :
    (principalBand hS a : Set E) = (Band.generated ({a} : Set E) : Set E) :=
  bandOfSchur_coe hS _

theorem mem_principalBand_self [CompleteSpace E] (hS : HasSchurProperty ℝ E) (a : E) :
    a ∈ principalBand hS a := by
  change a ∈ (principalBand hS a : Set E)
  rw [principalBand_coe]
  exact Band.subset_generated _ (Set.mem_singleton a)

theorem principalBand_submodule [CompleteSpace E] (hS : HasSchurProperty ℝ E)
    {a : E} (ha : IsLatticeAtom a) :
    (principalBand hS a).toSubmodule = Submodule.span ℝ ({a} : Set E) := by
  have heq : (principalBand hS a).toSubmodule = (Band.generated ({a} : Set E)).toSubmodule :=
    SetLike.coe_injective (principalBand_coe hS a)
  exact heq.trans (atom_band_eq_span hS ha)

theorem finiteDimensional_principalBand [CompleteSpace E] (hS : HasSchurProperty ℝ E)
    {a : E} (ha : IsLatticeAtom a) : FiniteDimensional ℝ (principalBand hS a).toSubmodule := by
  change @FiniteDimensional ℝ (principalBand hS a).toSubmodule _ _ (Submodule.module _)
  rw [principalBand_submodule hS ha]
  infer_instance

theorem sup_submodule (B C : ProjectionBand E) :
    (B ⊔ C).toSubmodule = B.toSubmodule ⊔ C.toSubmodule := by
  ext x
  change x ∈ ((B.toBand ⊔ C.toBand : Band E) : Set E) ↔ _
  rw [ProjectionBand.coe_band_sup_eq_add, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, heq⟩
    exact ⟨y, hy, z, hz, heq.symm⟩
  · rintro ⟨y, hy, z, hz, heq⟩
    exact ⟨y, hy, z, hz, heq.symm⟩

theorem finiteDimensional_sup (B C : ProjectionBand E)
    [FiniteDimensional ℝ B.toSubmodule] [FiniteDimensional ℝ C.toSubmodule] :
    FiniteDimensional ℝ (B ⊔ C).toSubmodule := by
  change @FiniteDimensional ℝ (B ⊔ C).toSubmodule _ _ (Submodule.module _)
  rw [sup_submodule]
  infer_instance

/-- Finite suprema retain finite rank. -/
theorem finiteDimensional_finset_sup {ι : Type*} (s : Finset ι) (B : ι → ProjectionBand E)
    (hB : ∀ i ∈ s, FiniteDimensional ℝ (B i).toSubmodule) :
    FiniteDimensional ℝ (s.sup B).toSubmodule := by
  classical
  change @FiniteDimensional ℝ (s.sup B).toSubmodule _ _ (Submodule.module _)
  induction s using Finset.induction_on with
  | empty =>
    change FiniteDimensional ℝ (⊥ : Submodule ℝ E)
    infer_instance
  | @insert a s ha ih =>
    rw [Finset.sup_insert]
    let := hB a (Finset.mem_insert_self a s)
    let := ih (fun i hi => hB i (Finset.mem_insert_of_mem hi))
    exact finiteDimensional_sup _ _

def cumulative (B : ℕ → ProjectionBand E) (n : ℕ) : ProjectionBand E :=
  (Finset.range (n + 1)).sup B

theorem cumulative_mono (B : ℕ → ProjectionBand E) : Monotone (cumulative B) := by
  intro m n hmn
  exact Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hmn 1))

theorem le_cumulative (B : ℕ → ProjectionBand E) (n : ℕ) : B n ≤ cumulative B n :=
  Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- Atomicity and eventual coverage by actual bands give strong convergence.
This proves coverage is analytically sufficient, rather than assuming a basis. -/
theorem tendsto_projection_of_atomic_cover [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (hA : IsAtomicLattice E)
    (B : ℕ → ProjectionBand E) (hmono : Monotone B)
    (hcover : ∀ a : E, IsLatticeAtom a → ∃ n, a ∈ B n) (x : E) :
    Tendsto (fun n => projection (B n) x) atTop (𝓝 x) := by
  have hpos (x : E) (hx : 0 ≤ x) :
      Tendsto (fun n => projection (B n) x) atTop (𝓝 x) := by
    let r : ℕ → E := fun n => x - projection (B n) x
    have hr : ∀ n, 0 ≤ r n := fun n => sub_nonneg.mpr (projection_le_self (B n) hx)
    have hanti : Antitone r := fun m n hmn =>
      sub_le_sub_left (projection_mono (hmono hmn) hx) x
    have hglb : IsGLB (Set.range r) 0 := by
      refine ⟨by rintro _ ⟨n, rfl⟩; exact hr n, ?_⟩
      intro u hu
      by_contra hbad
      have hu0 : u⁺ ≠ 0 := fun heq => hbad (posPart_eq_zero.mp heq)
      obtain ⟨a, ha, hau⟩ := hA u⁺ (lt_of_le_of_ne (posPart_nonneg u) hu0.symm)
      obtain ⟨N, haB⟩ := hcover a ha
      have ha_le : a ≤ r N := hau.trans (sup_le (hu (Set.mem_range_self N)) (hr N))
      have haD : a ∈ disjointComplement (B N : Set E) :=
        (Band.disjointComplement (B N : Set E)).solid
          ((B N).id_sub_bandProjection_mem x) ha.nonneg ha_le
      exact ha.ne_zero (Set.mem_singleton_iff.mp
        (disjointComplement_inter_eq_zero (B N : Set E) ⟨haB, haD⟩))
    have hlim := SchurLattice.tendsto_zero_of_antitone_isGLB hS r hanti hglb
    simpa only [r, sub_sub_cancel, sub_zero] using
      (tendsto_const_nhds (x := x)).sub hlim
  have hp := hpos x⁺ (posPart_nonneg x)
  have hn := hpos x⁻ (negPart_nonneg x)
  simpa only [← map_sub, posPart_sub_negPart] using hp.sub hn

/-- Increments of increasing band projections are positive operators. -/
theorem positive_difference (B : ℕ → ProjectionBand E) (hmono : Monotone B) (j : ℕ) :
    Positive (UnconditionalDecomposition.difference (fun n => projection (B n)) j).toLinearMap := by
  intro x hx
  cases j with
  | zero => exact projection_nonneg (B 0) hx
  | succ j =>
    exact sub_nonneg.mpr (projection_mono (hmono (Nat.le_succ j)) hx)

/-- Finite sign transforms of increasing band projections are contractive.
Their positive differences add to a positive contraction dominated by the identity. -/
theorem norm_signed_difference_sum_le (B : ℕ → ProjectionBand E) (hmono : Monotone B)
    (N : ℕ) (ε : ℕ → ℝ) (x : E) (hε : ∀ j, ε j = 1 ∨ ε j = -1) :
    ‖∑ j ∈ Finset.range (N + 1), ε j •
      UnconditionalDecomposition.difference (fun n => projection (B n)) j x‖ ≤ ‖x‖ := by
  let P : ℕ → E →L[ℝ] E := fun n => projection (B n)
  let d := UnconditionalDecomposition.difference P
  have hd (j : ℕ) : |d j x| ≤ d j |x| :=
    Positive.abs_le_map_abs (positive_difference B hmono j) x
  have hb (j : ℕ) : ε j • d j x ≤ d j |x| := by
    rcases hε j with he | he
    · simpa only [he, one_smul] using (le_abs_self (d j x)).trans (hd j)
    · simpa only [he, neg_smul, one_smul] using (neg_le_abs (d j x)).trans (hd j)
  have hbn (j : ℕ) : -(ε j • d j x) ≤ d j |x| := by
    rcases hε j with he | he
    · simpa only [he, one_smul] using (neg_le_abs (d j x)).trans (hd j)
    · simpa only [he, neg_smul, one_smul, neg_neg] using
        (le_abs_self (d j x)).trans (hd j)
  apply norm_le_norm_of_abs_le_abs
  change |∑ j ∈ Finset.range (N + 1), ε j • d j x| ≤ |x|
  apply le_trans (show |∑ j ∈ Finset.range (N + 1), ε j • d j x| ≤
      ∑ j ∈ Finset.range (N + 1), d j |x| from ?_) ?_
  · rw [abs]
    apply sup_le (Finset.sum_le_sum (fun j _ => hb j))
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun j _ => hbn j)
  · change (∑ j ∈ Finset.range (N + 1), UnconditionalDecomposition.difference P j |x|) ≤ |x|
    rw [UnconditionalRNP.sum_difference_apply]
    exact projection_le_self (B N) (abs_nonneg x)

/-- A separable Schur Banach lattice admits an increasing sequence of finite
dimensional bands covering every atom. No atomicity hypothesis is used here. -/
theorem exists_finiteDimensional_band_cover [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (hS : HasSchurProperty ℝ E) :
    ∃ B : ℕ → ProjectionBand E, Monotone B ∧
      (∀ n, FiniteDimensional ℝ (B n).toSubmodule) ∧
      ∀ a : E, IsLatticeAtom a → ∃ n, a ∈ B n := by
  classical
  let : Countable (normalizedLatticeAtoms E) := normalizedLatticeAtoms_countable.to_subtype
  let : Encodable (normalizedLatticeAtoms E) := Encodable.ofCountable _
  let C : ℕ → ProjectionBand E := fun n =>
    (Encodable.decode n : Option (normalizedLatticeAtoms E)).elim ⊥ (fun a => principalBand hS a)
  have hopt (o : Option (normalizedLatticeAtoms E)) :
      FiniteDimensional ℝ (o.elim (⊥ : ProjectionBand E) (fun a => principalBand hS a)).toSubmodule := by
    cases o with
    | none =>
      change FiniteDimensional ℝ (⊥ : Submodule ℝ E)
      infer_instance
    | some a => exact finiteDimensional_principalBand hS a.prop.1
  have hC (n : ℕ) : FiniteDimensional ℝ (C n).toSubmodule := hopt _
  refine ⟨cumulative C, cumulative_mono C, fun n =>
    finiteDimensional_finset_sup _ C (fun j _ => hC j), ?_⟩
  intro a ha
  let b : normalizedLatticeAtoms E := ⟨‖a‖⁻¹ • a, ha.normalize, ha.norm_normalize⟩
  let n := Encodable.encode b
  have hn : C n = principalBand hS b := by simp only [C, n, Encodable.encodek, Option.elim_some]
  have hb : (b : E) ∈ cumulative C n :=
    le_cumulative C n (hn.symm ▸ mem_principalBand_self hS b)
  refine ⟨n, ?_⟩
  change a ∈ (cumulative C n).toSubmodule
  have hmem := (cumulative C n).toSubmodule.smul_mem ‖a‖ hb
  simpa only [b, smul_inv_smul₀ (norm_ne_zero_iff.mpr ha.ne_zero)] using hmem

/-- Full vector-measure RNP for a separable Schur Banach lattice, under the
explicit assertion that every positive nonzero vector dominates an atom. -/
theorem hasRadonNikodymProperty_of_atomic [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (hS : HasSchurProperty ℝ E)
    (hA : IsAtomicLattice E) : HasRadonNikodymProperty.{u, v} E := by
  obtain ⟨B, hmono, hfinite, hcover⟩ := exists_finiteDimensional_band_cover hS
  apply UnconditionalRNP.hasRadonNikodymProperty_of_schur_unconditional_projections
    hS (fun n => projection (B n))
  · intro n
    rw [range_projection]
    exact hfinite n
  · intro m n hmn
    exact projection_comp_of_le (hmono hmn)
  · exact tendsto_projection_of_atomic_cover hS hA B hmono hcover
  · exact zero_le_one
  · intro N ε x hε
    simpa only [one_mul] using norm_signed_difference_sum_le B hmono N ε x hε

end PL1.AtomicBandDecomposition
