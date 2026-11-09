import PL1.ALOrder
import PL1.AtomicBandDecomposition
import PL1.SchurApproximation

/-! # Actual scalar coordinates of atomic AL spaces -/

noncomputable section
open Filter TopologicalSpace
open scoped Topology BigOperators

namespace PL1.ALAtomic
open AtomicBandDecomposition ALOrder

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E] [CompleteSpace E]
/-- A positive element of the principal band of an atom lies on its ray.
The proof uses norm convergence of its actual truncated principal-ideal net. -/
theorem mem_span_of_mem_atom_band_nonneg
    (hAL : ALRenorming.IsALNorm E) {a x : E} (ha : IsLatticeAtom a)
    (hx : 0 ≤ x) (hxa : x ∈ Band.generated ({a} : Set E)) :
    x ∈ Submodule.span ℝ ({a} : Set E) := by
  let y : ℕ → E := fun n => x ⊓ (n : ℝ) • a
  have hy : ∀ n, 0 ≤ y n := fun n =>
    le_inf hx (smul_nonneg (Nat.cast_nonneg _) ha.nonneg)
  have hmono : Monotone y := by
    intro m n hmn
    exact inf_le_inf_left _ (smul_le_smul_of_nonneg_right (Nat.cast_le.mpr hmn) ha.nonneg)
  obtain ⟨z, hz⟩ := ALOrder.exists_tendsto_of_monotone_net_norm_bounded hAL y hmono ‖x‖
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
theorem atom_band_eq_span (hAL : ALRenorming.IsALNorm E)
    {a : E} (ha : IsLatticeAtom a) :
    (Band.generated ({a} : Set E)).toSubmodule = Submodule.span ℝ ({a} : Set E) := by
  apply le_antisymm
  · intro x hx
    have hp := mem_span_of_mem_atom_band_nonneg hAL ha (posPart_nonneg x)
      ((Band.generated ({a} : Set E)).toOrderIdeal.posPart_mem hx)
    have hn := mem_span_of_mem_atom_band_nonneg hAL ha (negPart_nonneg x)
      ((Band.generated ({a} : Set E)).toOrderIdeal.negPart_mem hx)
    simpa only [posPart_sub_negPart] using (Submodule.span ℝ ({a} : Set E)).sub_mem hp hn
  · apply Submodule.span_le.mpr
    intro x hx
    exact Band.subset_generated _ hx


theorem principalBand_submodule (hAL : ALRenorming.IsALNorm E)
    {a : E} (ha : IsLatticeAtom a) :
    (ALOrder.principalBand hAL a).toSubmodule = Submodule.span ℝ ({a} : Set E) := by
  have heq : (ALOrder.principalBand hAL a).toSubmodule =
      (Band.generated ({a} : Set E)).toSubmodule :=
    SetLike.coe_injective (ALOrder.principalBand_coe hAL a)
  exact heq.trans (atom_band_eq_span hAL ha)

variable [TopologicalSpace.SeparableSpace E]

private instance atomsCountable : Countable (normalizedLatticeAtoms E) :=
  normalizedLatticeAtoms_countable.to_subtype

private noncomputable instance atomsEncodable : Encodable (normalizedLatticeAtoms E) :=
  Encodable.ofCountable _

/-- Each normalized atom is listed exactly once; unused indices carry the zero band. -/
def atomBand (hAL : ALRenorming.IsALNorm E) (n : ℕ) : ProjectionBand E :=
  (Encodable.decode₂ (normalizedLatticeAtoms E) n).elim ⊥
    (fun a => ALOrder.principalBand hAL a)

def atomProjection (hAL : ALRenorming.IsALNorm E) (n : ℕ) : E →L[ℝ] E :=
  projection (atomBand hAL n)

theorem atomProjection_eq_smul (hAL : ALRenorming.IsALNorm E) (n : ℕ) (x : E)
    {a : normalizedLatticeAtoms E}
    (ha : Encodable.decode₂ (normalizedLatticeAtoms E) n = some a) :
    ∃ t : ℝ, atomProjection hAL n x = t • (a : E) := by
  have hm := projection_mem (atomBand hAL n) x
  change atomProjection hAL n x ∈ (atomBand hAL n).toSubmodule at hm
  rw [show atomBand hAL n = ALOrder.principalBand hAL a by simp [atomBand, ha],
    principalBand_submodule hAL a.property.1] at hm
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hm
  exact ⟨t, ht.symm⟩

theorem atomProjection_eq_zero (hAL : ALRenorming.IsALNorm E) (n : ℕ) (x : E)
    (ha : Encodable.decode₂ (normalizedLatticeAtoms E) n = none) :
    atomProjection hAL n x = 0 := by
  have hm := projection_mem (atomBand hAL n) x
  change atomProjection hAL n x ∈ (atomBand hAL n).toSubmodule at hm
  rw [show atomBand hAL n = ⊥ by simp [atomBand, ha]] at hm
  exact hm

theorem atomProjection_pairwise (hAL : ALRenorming.IsALNorm E) (x y : E) :
    Pairwise (fun m n => IsVLDisjoint (atomProjection hAL m x) (atomProjection hAL n y)) := by
  intro m n hmn
  cases hm : Encodable.decode₂ (normalizedLatticeAtoms E) m with
  | none => rw [atomProjection_eq_zero hAL m x hm]; exact isVLDisjoint_zero_left _
  | some a =>
    cases hn : Encodable.decode₂ (normalizedLatticeAtoms E) n with
    | none => rw [atomProjection_eq_zero hAL n y hn]; exact isVLDisjoint_zero_right _
    | some b =>
      have hab : (a : E) ≠ (b : E) := by
        intro heq
        have hsub : a = b := Subtype.ext heq
        exact hmn ((Encodable.decode₂_eq_some.mp hm).symm.trans
          (hsub ▸ Encodable.decode₂_eq_some.mp hn))
      obtain ⟨s, hs⟩ := atomProjection_eq_smul hAL m x hm
      obtain ⟨t, ht⟩ := atomProjection_eq_smul hAL n y hn
      rw [hs, ht]
      exact ((a.property.1.isVLDisjoint_of_norm_eq_one b.property.1
        a.property.2 b.property.2 hab).smul_left s).smul_right t

def coordinate (hAL : ALRenorming.IsALNorm E) (n : ℕ) : E →L[ℝ] ℝ :=
  (normFunctional hAL).comp (atomProjection hAL n)

theorem norm_coordinate (hAL : ALRenorming.IsALNorm E) (n : ℕ) (x : E) :
    ‖coordinate hAL n x‖ = ‖atomProjection hAL n x‖ := by
  change ‖normFunctional hAL (atomProjection hAL n x)‖ = _
  cases hn : Encodable.decode₂ (normalizedLatticeAtoms E) n with
  | none => simp [atomProjection_eq_zero hAL n x hn]
  | some a =>
    obtain ⟨t, ht⟩ := atomProjection_eq_smul hAL n x hn
    rw [ht, map_smul, norm_smul, norm_smul,
      normFunctional_nonneg hAL a.property.1.nonneg]
    simp only [norm_norm]

theorem sum_atomProjection_le (hAL : ALRenorming.IsALNorm E)
    {x : E} (hx : 0 ≤ x) (N : ℕ) :
    (∑ n ∈ Finset.range N, atomProjection hAL n x) ≤ x := by
  by_cases hN : N = 0
  · simpa [hN] using hx
  rw [← Fin.sum_univ_eq_sum_range (fun n => atomProjection hAL n x)]
  have hp (i : Fin N) : 0 ≤ atomProjection hAL i x := projection_nonneg _ hx
  rw [sum_eq_sup_of_pairwise_isVLDisjoint_of_nonneg (Nat.pos_of_ne_zero hN)
    hp
    (fun i j hij => atomProjection_pairwise hAL x x (fun h => hij (Fin.ext h)))]
  exact Finset.sup'_le _ _ (fun i _ => projection_le_self (atomBand hAL i) hx)

omit [NormedVectorLattice E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E] in
theorem norm_sum_nonneg (hAL : ALRenorming.IsALNorm E) {ι : Type*}
    (s : Finset ι) (x : ι → E) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ‖∑ i ∈ s, x i‖ = ∑ i ∈ s, ‖x i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      hAL _ _ (hx i (Finset.mem_insert_self i s))
        (Finset.sum_nonneg fun j hj => hx j (Finset.mem_insert_of_mem hj))]
    rw [ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))]

theorem sum_norm_atomProjection_le (hAL : ALRenorming.IsALNorm E) (x : E) (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖atomProjection hAL n x‖) ≤ ‖x‖ := by
  have hp (n : ℕ) : |atomProjection hAL n x| ≤ atomProjection hAL n |x| :=
    Positive.abs_le_map_abs (fun y hy => projection_nonneg (atomBand hAL n) hy) x
  calc
    ∑ n ∈ Finset.range N, ‖atomProjection hAL n x‖ ≤
        ∑ n ∈ Finset.range N, ‖atomProjection hAL n |x|‖ := by
      apply Finset.sum_le_sum
      intro n _
      exact norm_le_norm_of_abs_le_abs ((hp n).trans (le_abs_self _))
    _ = ‖∑ n ∈ Finset.range N, atomProjection hAL n |x|‖ :=
      (norm_sum_nonneg hAL _ _ (fun n _ => projection_nonneg _ (abs_nonneg x))).symm
    _ ≤ ‖x‖ := norm_le_norm_of_abs_le_abs (by
      have hpos : 0 ≤ ∑ n ∈ Finset.range N, atomProjection hAL n |x| :=
        Finset.sum_nonneg fun n _ => projection_nonneg _ (abs_nonneg x)
      rw [abs_of_nonneg hpos]
      exact sum_atomProjection_le hAL (abs_nonneg x) N)

theorem summable_norm_atomProjection (hAL : ALRenorming.IsALNorm E) (x : E) :
    Summable (fun n => ‖atomProjection hAL n x‖) :=
  summable_of_sum_range_le (fun _ => norm_nonneg _) (sum_norm_atomProjection_le hAL x)

theorem atomBand_cover (hAL : ALRenorming.IsALNorm E) {a : E} (ha : IsLatticeAtom a) :
    ∃ n, a ∈ atomBand hAL n := by
  let b : normalizedLatticeAtoms E := ⟨‖a‖⁻¹ • a, ha.normalize, ha.norm_normalize⟩
  refine ⟨Encodable.encode b, ?_⟩
  have hb : atomBand hAL (Encodable.encode b) = ALOrder.principalBand hAL b := by
    simp [atomBand, Encodable.decode₂_encode]
  rw [hb]
  have hm := (ALOrder.principalBand hAL b).toSubmodule.smul_mem ‖a‖
    (ALOrder.mem_principalBand_self hAL b)
  change a ∈ (ALOrder.principalBand hAL b).toSubmodule
  simpa only [b, smul_inv_smul₀ (norm_ne_zero_iff.mpr ha.ne_zero)] using hm

/-- Atomicity forces the actual positive atom projections to exhaust each vector. -/
theorem tendsto_sum_atomProjection (hAL : ALRenorming.IsALNorm E) (hA : IsAtomicLattice E)
    (x : E) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, atomProjection hAL n x) atTop (𝓝 x) := by
  have hpos (x : E) (hx : 0 ≤ x) :
      Tendsto (fun N => ∑ n ∈ Finset.range N, atomProjection hAL n x) atTop (𝓝 x) := by
    let z := ∑' n, atomProjection hAL n x
    have ht : Tendsto (fun N => ∑ n ∈ Finset.range N, atomProjection hAL n x)
        atTop (𝓝 z) := (summable_norm_atomProjection hAL x).of_norm.hasSum.tendsto_sum_nat
    have hzx : z ≤ x := le_of_tendsto' ht (sum_atomProjection_le hAL hx)
    have hnp (n : ℕ) : atomProjection hAL n x ≤ z := by
      have hm : Monotone (fun N => ∑ n ∈ Finset.range N, atomProjection hAL n x) := by
        apply monotone_nat_of_le_succ
        intro N
        rw [Finset.sum_range_succ]
        exact le_add_of_nonneg_right (projection_nonneg _ hx)
      have hn : atomProjection hAL n x ≤
          ∑ j ∈ Finset.range (n + 1), atomProjection hAL j x :=
        Finset.single_le_sum (fun j _ => projection_nonneg _ hx) (Finset.mem_range.mpr (Nat.lt_succ_self n))
      exact hn.trans ((isLUB_of_tendsto_atTop hm ht).1 (Set.mem_range_self (n + 1)))
    have heq : z = x := by
      by_contra hne
      have hr : 0 < x - z := lt_of_le_of_ne (sub_nonneg.mpr hzx)
        (fun he => hne (sub_eq_zero.mp he.symm).symm)
      obtain ⟨a, ha, har⟩ := hA _ hr
      obtain ⟨n, han⟩ := atomBand_cover hAL ha
      have hbound : a ≤ x - atomProjection hAL n x :=
        har.trans (sub_le_sub_left (hnp n) x)
      have had : a ∈ disjointComplement (atomBand hAL n : Set E) :=
        (Band.disjointComplement (atomBand hAL n : Set E)).solid
          ((atomBand hAL n).id_sub_bandProjection_mem x) ha.nonneg hbound
      exact ha.ne_zero (Set.mem_singleton_iff.mp
        (disjointComplement_inter_eq_zero _ ⟨han, had⟩))
    exact heq ▸ ht
  have hp := hpos x⁺ (posPart_nonneg x)
  have hn := hpos x⁻ (negPart_nonneg x)
  simpa only [← Finset.sum_sub_distrib, ← map_sub, posPart_sub_negPart] using hp.sub hn

theorem tsum_atomProjection (hAL : ALRenorming.IsALNorm E) (hA : IsAtomicLattice E)
    (x : E) : (∑' n, atomProjection hAL n x) = x :=
  tendsto_nhds_unique (summable_norm_atomProjection hAL x).of_norm.hasSum.tendsto_sum_nat
    (tendsto_sum_atomProjection hAL hA x)

theorem summable_norm_coordinate (hAL : ALRenorming.IsALNorm E) (x : E) :
    Summable (fun n => ‖coordinate hAL n x‖) := by
  simpa only [norm_coordinate] using summable_norm_atomProjection hAL x

def coordinateLinear (hAL : ALRenorming.IsALNorm E) : E →ₗ[ℝ] Ell1 ℝ where
  toFun x := ⟨fun n => coordinate hAL n x, memℓp_gen (by simpa using summable_norm_coordinate hAL x)⟩
  map_add' x y := by apply lp.ext; funext n; exact map_add (coordinate hAL n) x y
  map_smul' c x := by apply lp.ext; funext n; exact map_smul (coordinate hAL n) c x

theorem norm_coordinateLinear_le (hAL : ALRenorming.IsALNorm E) (x : E) :
    ‖coordinateLinear hAL x‖ ≤ ‖x‖ := by
  rw [L1Sum.norm_eq_tsum]
  change (∑' n, ‖coordinate hAL n x‖) ≤ ‖x‖
  simp_rw [norm_coordinate]
  exact le_of_tendsto' (summable_norm_atomProjection hAL x).hasSum.tendsto_sum_nat
    (sum_norm_atomProjection_le hAL x)

theorem norm_coordinateLinear (hAL : ALRenorming.IsALNorm E) (hA : IsAtomicLattice E)
    (x : E) : ‖coordinateLinear hAL x‖ = ‖x‖ := by
  refine le_antisymm (norm_coordinateLinear_le hAL x) ?_
  rw [L1Sum.norm_eq_tsum]
  change ‖x‖ ≤ ∑' n, ‖coordinate hAL n x‖
  simp_rw [norm_coordinate]
  have h := norm_tsum_le_tsum_norm (summable_norm_atomProjection hAL x)
  rwa [tsum_atomProjection hAL hA x] at h

/-- The actual scalar atom coordinates form an isometric embedding into ℓ₁. -/
def coordinateIsometry (hAL : ALRenorming.IsALNorm E) (hA : IsAtomicLattice E) :
    E →ₗᵢ[ℝ] Ell1 ℝ :=
  { coordinateLinear hAL with norm_map' := norm_coordinateLinear hAL hA }

theorem containsIsomorphicCopy_ell1 (hAL : ALRenorming.IsALNorm E)
    (hA : IsAtomicLattice E) : ContainsIsomorphicCopy ℝ E (Ell1 ℝ) := by
  let J := (coordinateIsometry hAL hA).toContinuousLinearMap
  have hJ : Topology.IsClosedEmbedding J := (coordinateIsometry hAL hA).isometry.isClosedEmbedding
  exact ⟨J.range, hJ.isClosed_range, ⟨J.equivRange hJ.injective hJ.isClosed_range⟩⟩

/-- A separable atomic complete AL space has the Schur property. -/
theorem hasSchurProperty (hAL : ALRenorming.IsALNorm E) (hA : IsAtomicLattice E) :
    HasSchurProperty ℝ E :=
  (ell1_hasSchurProperty ℝ).of_containsIsomorphicCopy (containsIsomorphicCopy_ell1 hAL hA)

end PL1.ALAtomic

