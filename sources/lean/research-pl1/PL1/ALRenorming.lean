import PL1.LatticeRenorming
import BanLat.RieszDec
import BanLat.Operators.Positive

/-!
# Positive decomposition renorming

The finite estimate in this file quantifies over every positive family. It is
stronger than a disjoint-family estimate; no implication between those two
estimates is assumed or asserted here. Its positive-decomposition supremum
constructs a genuine equivalent AL norm.
-/

noncomputable section
open scoped BigOperators

namespace PL1.ALRenorming

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- The original norm is additive on the positive cone. -/
def IsALNorm (E : Type*) [NormedAddCommGroup E] [Lattice E] : Prop :=
  ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖

/-- A uniform lower-one estimate for all positive finite families. -/
def PositiveLowerOne (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E), (∀ i, 0 ≤ x i) →
    ∑ i, ‖x i‖ ≤ C * ‖∑ i, x i‖

def decompositionValues (u : E) : Set ℝ :=
  {r | ∃ (n : ℕ) (x : Fin n → E), (∀ i, 0 ≤ x i) ∧
    (∑ i, x i) ≤ u ∧ r = ∑ i, ‖x i‖}

def variation (u : E) : ℝ := sSup (decompositionValues u)

omit [IsOrderedAddMonoid E] [NormedVectorLattice E] in
theorem zero_mem_decompositionValues {u : E} (hu : 0 ≤ u) :
    0 ∈ decompositionValues u :=
  ⟨0, Fin.elim0, fun i => i.elim0, by simpa using hu, by simp⟩

theorem decompositionValues_bddAbove {C : ℝ} (hC : PositiveLowerOne (E := E) C)
    {u : E} (hu : 0 ≤ u) : BddAbove (decompositionValues u) := by
  refine ⟨C * ‖u‖, ?_⟩
  rintro r ⟨n, x, hx, hxu, rfl⟩
  exact (hC.2 n x hx).trans (mul_le_mul_of_nonneg_left
    (norm_le_norm_of_abs_le_abs (by
      simpa only [abs_of_nonneg (Finset.sum_nonneg fun i _ => hx i),
        abs_of_nonneg hu] using hxu)) hC.1)

theorem variation_nonneg {C : ℝ} (hC : PositiveLowerOne (E := E) C)
    {u : E} (hu : 0 ≤ u) : 0 ≤ variation u :=
  le_csSup (decompositionValues_bddAbove hC hu) (zero_mem_decompositionValues hu)

theorem variation_le {C : ℝ} (hC : PositiveLowerOne (E := E) C)
    {u : E} (hu : 0 ≤ u) : variation u ≤ C * ‖u‖ := by
  apply csSup_le ⟨0, zero_mem_decompositionValues hu⟩
  rintro r ⟨n, x, hx, hxu, rfl⟩
  exact (hC.2 n x hx).trans (mul_le_mul_of_nonneg_left
    (norm_le_norm_of_abs_le_abs (by
      simpa only [abs_of_nonneg (Finset.sum_nonneg fun i _ => hx i),
        abs_of_nonneg hu] using hxu)) hC.1)

theorem norm_le_variation {C : ℝ} (hC : PositiveLowerOne (E := E) C)
    {u : E} (hu : 0 ≤ u) : ‖u‖ ≤ variation u := by
  apply le_csSup (decompositionValues_bddAbove hC hu)
  exact ⟨1, fun _ => u, fun _ => hu, by simp, by simp⟩

theorem variation_mono {C : ℝ} (hC : PositiveLowerOne (E := E) C)
    {u v : E} (hu : 0 ≤ u) (huv : u ≤ v) : variation u ≤ variation v := by
  apply csSup_le ⟨0, zero_mem_decompositionValues hu⟩
  rintro r ⟨n, x, hx, hxu, hr⟩
  exact le_csSup (decompositionValues_bddAbove hC (hu.trans huv))
    ⟨n, x, hx, hxu.trans huv, hr⟩

theorem variation_add {C : ℝ} (hC : PositiveLowerOne (E := E) C)
    (u v : E) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    variation (u + v) = variation u + variation v := by
  classical
  apply le_antisymm
  · apply csSup_le ⟨0, zero_mem_decompositionValues (add_nonneg hu hv)⟩
    rintro r ⟨n, x, hx, hsum, rfl⟩
    obtain ⟨a, b, ha, hb, has, hbs, hx'⟩ :=
      riesz_decomposition_sum_le x u v hx hu hv hsum
    calc
      ∑ i, ‖x i‖ ≤ ∑ i, (‖a i‖ + ‖b i‖) :=
        Finset.sum_le_sum fun i _ => by rw [hx' i]; exact norm_add_le _ _
      _ = (∑ i, ‖a i‖) + ∑ i, ‖b i‖ := Finset.sum_add_distrib
      _ ≤ variation u + variation v := add_le_add
        (le_csSup (decompositionValues_bddAbove hC hu) ⟨n, a, ha, has, rfl⟩)
        (le_csSup (decompositionValues_bddAbove hC hv) ⟨n, b, hb, hbs, rfl⟩)
  · apply le_of_forall_lt_imp_le_of_dense
    intro r hr
    have hr' : r - variation v < variation u := by linarith
    obtain ⟨a, ha, hbr⟩ := exists_lt_of_lt_csSup
      ⟨0, zero_mem_decompositionValues hu⟩ hr'
    have hr'' : r - a < variation v := by linarith
    obtain ⟨b, hb, hab⟩ := exists_lt_of_lt_csSup
      ⟨0, zero_mem_decompositionValues hv⟩ hr''
    obtain ⟨m, x, hx, hxu, rfl⟩ := ha
    obtain ⟨n, y, hy, hyv, rfl⟩ := hb
    have hm : (∑ i, ‖x i‖) + ∑ i, ‖y i‖ ∈ decompositionValues (u + v) := by
      refine ⟨m + n, Fin.addCases x y, ?_, ?_, ?_⟩
      · intro i
        exact Fin.addCases (fun j => by simpa using hx j)
          (fun j => by simpa using hy j) i
      · simpa [Fin.sum_univ_add] using add_le_add hxu hyv
      · simp [Fin.sum_univ_add]
    exact (by linarith : r ≤ (∑ i, ‖x i‖) + ∑ i, ‖y i‖).trans
      (le_csSup (decompositionValues_bddAbove hC (add_nonneg hu hv)) hm)

/-- The positive-decomposition gauge extends to a positive real functional. -/
def variationLinear {C : ℝ} (hC : PositiveLowerOne (E := E) C) : E →ₗ[ℝ] ℝ :=
  Positive.extension (fun _ hu => variation_nonneg hC hu) (variation_add hC)

theorem variationLinear_nonneg {C : ℝ} (hC : PositiveLowerOne (E := E) C)
    {u : E} (hu : 0 ≤ u) : variationLinear hC u = variation u :=
  Positive.extension_nonneg _ _ hu

theorem variationLinear_positive {C : ℝ} (hC : PositiveLowerOne (E := E) C) :
    Positive (variationLinear hC) := Positive.extension_positive _ _

/-- The solid AL seminorm associated to the constructed functional. -/
def seminorm {C : ℝ} (hC : PositiveLowerOne (E := E) C) : Seminorm ℝ E :=
  Seminorm.of (fun x => variationLinear hC |x|)
    (fun x y => by
      rw [← map_add]
      exact (Positive.monotone_iff.mpr (variationLinear_positive hC)) (abs_add_le x y))
    (fun a x => by simp only [abs_smul', map_smul, smul_eq_mul, Real.norm_eq_abs])

theorem seminorm_bounds {C : ℝ} (hC : PositiveLowerOne (E := E) C) (x : E) :
    ‖x‖ ≤ seminorm hC x ∧ seminorm hC x ≤ C * ‖x‖ := by
  change ‖x‖ ≤ variationLinear hC |x| ∧ variationLinear hC |x| ≤ C * ‖x‖
  rw [variationLinear_nonneg hC (abs_nonneg x)]
  simpa only [norm_abs_eq_norm] using
    And.intro (norm_le_variation hC (abs_nonneg x)) (variation_le hC (abs_nonneg x))

theorem seminorm_solid {C : ℝ} (hC : PositiveLowerOne (E := E) C)
    (x y : E) (hxy : |x| ≤ |y|) : seminorm hC x ≤ seminorm hC y :=
  (Positive.monotone_iff.mpr (variationLinear_positive hC)) hxy

theorem seminorm_add_of_nonneg {C : ℝ} (hC : PositiveLowerOne (E := E) C)
    (x y : E) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    seminorm hC (x + y) = seminorm hC x + seminorm hC y := by
  change variationLinear hC |x + y| = variationLinear hC |x| + variationLinear hC |y|
  rw [abs_of_nonneg (add_nonneg hx hy), abs_of_nonneg hx, abs_of_nonneg hy, map_add]

theorem seminorm_separates {C : ℝ} (hC : PositiveLowerOne (E := E) C)
    (x : E) (hx : seminorm hC x = 0) : x = 0 := by
  exact norm_eq_zero.mp (le_antisymm (hx ▸ (seminorm_bounds hC x).1) (norm_nonneg x))

/-- The actual vector-space copy carrying the constructed AL norm. -/
abbrev Space {C : ℝ} (hC : PositiveLowerOne (E := E) C) :=
  LatticeRenorming.Space (seminorm hC) (seminorm_separates hC)

def equiv {C : ℝ} (hC : PositiveLowerOne (E := E) C) : E ≃L[ℝ] Space hC :=
  LatticeRenorming.equiv _ _ 1 C (by norm_num)
    (fun x => by simpa only [one_mul] using seminorm_bounds hC x)

@[reducible] def normedVectorLattice {C : ℝ} (hC : PositiveLowerOne (E := E) C) :
    NormedVectorLattice (Space hC) :=
  LatticeRenorming.normedVectorLattice _ _ (seminorm_solid hC)

theorem completeSpace [CompleteSpace E] {C : ℝ}
    (hC : PositiveLowerOne (E := E) C) : CompleteSpace (Space hC) :=
  LatticeRenorming.completeSpace _ _ 1 C (by norm_num)
    (fun x => by simpa only [one_mul] using seminorm_bounds hC x)

theorem separableSpace [TopologicalSpace.SeparableSpace E] {C : ℝ}
    (hC : PositiveLowerOne (E := E) C) : TopologicalSpace.SeparableSpace (Space hC) :=
  LatticeRenorming.separableSpace _ _ 1 C (by norm_num)
    (fun x => by simpa only [one_mul] using seminorm_bounds hC x)

theorem isALNorm {C : ℝ} (hC : PositiveLowerOne (E := E) C) : IsALNorm (Space hC) :=
  seminorm_add_of_nonneg hC

end PL1.ALRenorming
