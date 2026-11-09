import Mathlib.Topology.Instances.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.SymmDiff
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The countable sign group and its Walsh characters

The two-element group is represented by `Multiplicative (ZMod 2)`.
Its elements 0 and 1 correspond to the signs +1 and -1. Thus the group below
is precisely the countable sign group used in the manuscript, with zero-based
coordinates. Its measure is the Haar measure normalized on the whole compact
group, without an assumption of independence.
-/

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal symmDiff

namespace PL1
namespace Walsh

abbrev Sign := Multiplicative (ZMod 2)
instance : MeasurableSpace Sign := borel Sign
instance : BorelSpace Sign := ⟨rfl⟩

/-- The product uses Mathlib's canonical Pi measurable space. Since the index
is countable and the factors are finite discrete spaces, it is also Borel. -/
abbrev Group := ℕ → Sign

def haar : Measure Group := Measure.haarMeasure ⊤

instance : IsProbabilityMeasure haar := by
  constructor
  simpa only [haar, PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts Group)))

instance : Measure.IsHaarMeasure haar := by
  unfold haar
  infer_instance

instance : haar.Regular := by
  unfold haar
  infer_instance

def signValue (a : Sign) : ℝ := if a.toAdd = 0 then 1 else -1

@[simp] theorem signValue_one : signValue 1 = 1 := by
  simp [signValue]

set_option backward.isDefEq.respectTransparency false in
theorem signValue_mul (a b : Sign) : signValue (a * b) = signValue a * signValue b := by
  change (if a.toAdd + b.toAdd = 0 then (1 : ℝ) else -1) = _
  generalize ha : a.toAdd = x
  generalize hb : b.toAdd = y
  simp only [signValue, ha, hb]
  fin_cases x <;> fin_cases y <;> norm_num [Fin.ext_iff, Fin.add_def]
  decide

@[simp] theorem norm_signValue (a : Sign) : ‖signValue a‖ = 1 := by
  unfold signValue
  split <;> norm_num

@[simp] theorem signValue_mul_self (a : Sign) : signValue a * signValue a = 1 := by
  unfold signValue
  split <;> norm_num

theorem signValue_eq_one_or_neg_one (a : Sign) : signValue a = 1 ∨ signValue a = -1 := by
  unfold signValue
  split <;> simp

set_option backward.isDefEq.respectTransparency false in
theorem signValue_injective : Function.Injective signValue := by
  intro a b hab
  have h : a.toAdd = b.toAdd := by
    generalize hx : a.toAdd = x
    generalize hy : b.toAdd = y
    have hh : (if x = 0 then (1 : ℝ) else -1) = if y = 0 then 1 else -1 := by
      simpa only [signValue, hx, hy] using hab
    fin_cases x <;> fin_cases y <;> norm_num [Fin.ext_iff] at *
  exact congrArg Multiplicative.ofAdd h

def character (F : Finset ℕ) (x : Group) : ℝ := ∏ j ∈ F, signValue (x j)

@[simp] theorem character_empty (x : Group) : character ∅ x = 1 := by
  simp [character]

@[simp] theorem character_one (F : Finset ℕ) : character F 1 = 1 := by
  simp [character]

@[simp] theorem character_singleton (j : ℕ) (x : Group) :
    character {j} x = signValue (x j) := by
  simp [character]

theorem character_mul (F : Finset ℕ) (x y : Group) :
    character F (x * y) = character F x * character F y := by
  simp only [character, Pi.mul_apply, signValue_mul, Finset.prod_mul_distrib]

@[simp] theorem norm_character (F : Finset ℕ) (x : Group) :
    ‖character F x‖ = 1 := by
  rw [character, norm_prod]
  simp only [norm_signValue, Finset.prod_const_one]

@[simp] theorem character_mul_self (F : Finset ℕ) (x : Group) :
    character F x * character F x = 1 := by
  rw [character, ← Finset.prod_mul_distrib]
  simp

/-- The Walsh multiplication law: repeated coordinates cancel. -/
theorem character_symmDiff (F H : Finset ℕ) (x : Group) :
    character (F ∆ H) x = character F x * character H x := by
  have hd : Disjoint (F ∆ H) (F ∩ H) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    rcases Finset.mem_symmDiff.mp hj with h | h
    · exact h.2 (Finset.mem_inter.mp hk).2
    · exact h.2 (Finset.mem_inter.mp hk).1
  have hu : (F ∆ H) ∪ (F ∩ H) = F ∪ H := by
    ext j
    by_cases hjF : j ∈ F <;> by_cases hjH : j ∈ H <;>
      simp [Finset.mem_symmDiff, hjF, hjH]
  have hp : character (F ∆ H) x * character (F ∩ H) x = character (F ∪ H) x := by
    simpa only [character, hu] using
      (Finset.prod_union hd (f := fun j => signValue (x j))).symm
  calc
    character (F ∆ H) x =
        (character (F ∆ H) x * character (F ∩ H) x) * character (F ∩ H) x := by
          rw [mul_assoc, character_mul_self, mul_one]
    _ = character (F ∪ H) x * character (F ∩ H) x := by rw [hp]
    _ = character F x * character H x := by
      exact Finset.prod_union_inter

theorem continuous_character (F : Finset ℕ) : Continuous (character F) := by
  apply continuous_finsetProd
  intro j hj
  exact (continuous_of_discreteTopology : Continuous signValue).comp
    (continuous_apply j : Continuous (fun x : Group => x j))

theorem integrable_character (F : Finset ℕ) : Integrable (character F) haar := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_character F).aestronglyMeasurable
  filter_upwards [] with x
  exact le_of_eq (norm_character F x)

/-- The group element which flips only coordinate j. -/
def flip (j : ℕ) : Group := Function.update 1 j (Multiplicative.ofAdd 1)

theorem character_flip_of_mem {F : Finset ℕ} {j : ℕ} (hj : j ∈ F) :
    character F (flip j) = -1 := by
  rw [character, Finset.prod_eq_single j]
  · norm_num [flip, signValue]
  · intro i hi hij
    simp [flip, Function.update_of_ne hij, signValue]
  · intro h
    exact (h hj).elim

theorem integral_character_eq_zero {F : Finset ℕ} (hF : F.Nonempty) :
    ∫ x, character F x ∂haar = 0 := by
  obtain ⟨j, hj⟩ := hF
  apply integral_eq_zero_of_mul_left_eq_neg (g := flip j)
  intro x
  rw [character_mul, character_flip_of_mem hj, neg_one_mul]

theorem integral_character (F : Finset ℕ) :
    ∫ x, character F x ∂haar = if F = ∅ then 1 else 0 := by
  by_cases hF : F = ∅
  · simp [hF]
  · simp [hF, integral_character_eq_zero (Finset.nonempty_iff_ne_empty.mpr hF)]

/-- Orthogonality with respect to the actual normalized Haar measure. -/
theorem integral_character_mul (F H : Finset ℕ) :
    ∫ x, character F x * character H x ∂haar = if F = H then 1 else 0 := by
  simp_rw [← character_symmDiff]
  simp [integral_character]

@[simp] theorem character_inv (F : Finset ℕ) (x : Group) :
    character F x⁻¹ = character F x := by
  have h : character F x⁻¹ * character F x = 1 := by
    rw [← character_mul, inv_mul_cancel, character_one]
  calc
    character F x⁻¹ = (character F x⁻¹ * character F x) * character F x := by
      rw [mul_assoc, character_mul_self, mul_one]
    _ = character F x := by rw [h, one_mul]

/-- Fourier coefficient of a positive measure at a Walsh character. -/
def coefficient (τ : Measure Group) (F : Finset ℕ) : ℝ :=
  ∫ x, character F x ∂τ

/-- Convolution on raw functions, before the later descent to equivalence classes in Lp. -/
def convolution (τ : Measure Group) (f : Group → ℝ) (x : Group) : ℝ :=
  ∫ y, f (x * y⁻¹) ∂τ

/-- Each Walsh character is an eigenfunction of convolution. -/
theorem convolution_character (τ : Measure Group) (F : Finset ℕ) (x : Group) :
    convolution τ (character F) x = coefficient τ F * character F x := by
  simp only [convolution, character_mul, character_inv, coefficient]
  rw [integral_const_mul, mul_comm]

/-- Walsh characters belong to every Lp space, including L-infinity. -/
theorem memLp_character (p : ℝ≥0∞) (F : Finset ℕ) : MemLp (character F) p haar := by
  apply MemLp.of_bound (continuous_character F).aestronglyMeasurable 1
  filter_upwards [] with x
  exact le_of_eq (norm_character F x)

/-- The actual a.e.-equivalence class of a Walsh character. -/
def characterLp (p : ℝ≥0∞) (F : Finset ℕ) : Lp ℝ p haar :=
  (memLp_character p F).toLp (character F)

theorem coeFn_characterLp (p : ℝ≥0∞) (F : Finset ℕ) :
    characterLp p F =ᵐ[haar] character F :=
  (memLp_character p F).coeFn_toLp

theorem inner_characterL2 (F H : Finset ℕ) :
    inner ℝ (characterLp 2 F) (characterLp 2 H) = if F = H then 1 else 0 := by
  rw [L2.inner_def]
  calc
    (∫ x, inner ℝ (characterLp 2 F x) (characterLp 2 H x) ∂haar) =
        ∫ x, character F x * character H x ∂haar := by
      apply integral_congr_ae
      filter_upwards [coeFn_characterLp 2 F, coeFn_characterLp 2 H] with x hx hy
      rw [hx, hy]
      simp [RCLike.inner_apply, mul_comm]
    _ = if F = H then 1 else 0 := integral_character_mul F H

/-- The Walsh vectors form an orthonormal family in genuine Haar L2. -/
theorem orthonormal_characterL2 : Orthonormal ℝ (characterLp 2) :=
  orthonormal_iff_ite.mpr inner_characterL2

/-- A Walsh character as a continuous function on the compact sign group. -/
def characterContinuous (F : Finset ℕ) : C(Group, ℝ) :=
  ⟨character F, continuous_character F⟩

@[simp] theorem characterContinuous_empty : characterContinuous ∅ = 1 := by
  ext x
  exact character_empty x

theorem characterContinuous_symmDiff (F H : Finset ℕ) :
    characterContinuous (F ∆ H) = characterContinuous F * characterContinuous H := by
  ext x
  exact character_symmDiff F H x

/-- The characters are a multiplicatively closed family containing 1. -/
def characterSubmonoid : Submonoid C(Group, ℝ) where
  carrier := Set.range characterContinuous
  one_mem' := ⟨∅, characterContinuous_empty⟩
  mul_mem' := by
    rintro f g ⟨F, rfl⟩ ⟨H, rfl⟩
    exact ⟨F ∆ H, characterContinuous_symmDiff F H⟩

/-- The real algebra of finite Walsh polynomials. -/
def polynomials : Subalgebra ℝ C(Group, ℝ) :=
  Algebra.adjoin ℝ (characterSubmonoid : Set C(Group, ℝ))

theorem polynomials_toSubmodule :
    polynomials.toSubmodule = Submodule.span ℝ (Set.range characterContinuous) := by
  rw [polynomials, Algebra.adjoin_eq_span, characterSubmonoid.closure_eq]
  rfl

theorem polynomials_separatesPoints : polynomials.SeparatesPoints := by
  intro x y hxy
  have hn : ∃ j, x j ≠ y j := by
    by_contra h
    apply hxy
    funext j
    exact not_not.mp (fun hj => h ⟨j, hj⟩)
  obtain ⟨j, hj⟩ := hn
  refine ⟨character {j}, ⟨characterContinuous {j}, ?_, rfl⟩, ?_⟩
  · exact Algebra.subset_adjoin ⟨{j}, rfl⟩
  · simpa only [character_singleton] using fun h => hj (signValue_injective h)

/-- Walsh polynomials are uniformly dense in all real continuous functions. -/
theorem polynomials_dense : Dense (polynomials : Set C(Group, ℝ)) := by
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    polynomials polynomials_separatesPoints
  rw [SetLike.ext'_iff] at h
  change closure (polynomials : Set C(Group, ℝ)) = Set.univ at h
  exact dense_iff_closure_eq.mpr h

theorem toLp_characterContinuous (p : ℝ≥0∞) [Fact (1 ≤ p)] (F : Finset ℕ) :
    ContinuousMap.toLp p haar ℝ (characterContinuous F) = characterLp p F := by
  apply Lp.ext
  exact (ContinuousMap.coeFn_toLp haar (characterContinuous F)).trans
    (coeFn_characterLp p F).symm

/-- Finite real Walsh polynomials are dense in every genuine Lp, 1 ≤ p < infinity. -/
theorem dense_span_characterLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense (Submodule.span ℝ (Set.range (characterLp p)) : Set (Lp ℝ p haar)) := by
  apply (ContinuousMap.toLp_denseRange (p := p) ℝ haar ℝ hp).dense_of_mapsTo
    (ContinuousMap.toLp p haar ℝ).continuous polynomials_dense
  intro f hf
  have hf' : f ∈ Submodule.span ℝ (Set.range characterContinuous) := by
    rw [← polynomials_toSubmodule]
    exact hf
  have him := Submodule.image_span_subset_span
    (ContinuousMap.toLp p haar ℝ).toLinearMap (Set.range characterContinuous) ⟨f, hf', rfl⟩
  have hr : (ContinuousMap.toLp p haar ℝ) '' Set.range characterContinuous =
      Set.range (characterLp p) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext (toLp_characterContinuous p))
  simpa only [ContinuousLinearMap.coe_coe, hr] using him

/-- The complete real Walsh Hilbert basis of Haar L2. -/
def hilbertBasis : HilbertBasis (Finset ℕ) ℝ (Lp ℝ 2 haar) :=
  HilbertBasis.mk orthonormal_characterL2 (by
    rw [Submodule.dense_iff_topologicalClosure_eq_top.mp
      (dense_span_characterLp 2 (by norm_num))])

@[simp] theorem hilbertBasis_apply (F : Finset ℕ) :
    hilbertBasis F = characterLp 2 F := by
  exact congrFun (HilbertBasis.coe_mk _ _) F

section Scalars

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The same sign-valued character, over either scalar field of the manuscript. -/
def scalarCharacter (F : Finset ℕ) (x : Group) : 𝕜 := (character F x : ℝ)

@[simp] theorem norm_scalarCharacter (F : Finset ℕ) (x : Group) :
    ‖scalarCharacter 𝕜 F x‖ = 1 := by
  simpa only [scalarCharacter, RCLike.norm_ofReal, Real.norm_eq_abs] using norm_character F x

theorem continuous_scalarCharacter (F : Finset ℕ) : Continuous (scalarCharacter 𝕜 F) :=
  RCLike.continuous_ofReal.comp (continuous_character F)

theorem scalarCharacter_symmDiff (F H : Finset ℕ) (x : Group) :
    scalarCharacter 𝕜 (F ∆ H) x = scalarCharacter 𝕜 F x * scalarCharacter 𝕜 H x := by
  simp only [scalarCharacter, character_symmDiff, RCLike.ofReal_mul]

@[simp] theorem star_scalarCharacter (F : Finset ℕ) (x : Group) :
    star (scalarCharacter 𝕜 F x) = scalarCharacter 𝕜 F x := by
  simp [scalarCharacter]

theorem memLp_scalarCharacter (p : ℝ≥0∞) (F : Finset ℕ) :
    MemLp (scalarCharacter 𝕜 F) p haar := by
  apply MemLp.of_bound (continuous_scalarCharacter 𝕜 F).aestronglyMeasurable 1
  filter_upwards [] with x
  exact le_of_eq (norm_scalarCharacter 𝕜 F x)

def scalarCharacterLp (p : ℝ≥0∞) (F : Finset ℕ) : Lp 𝕜 p haar :=
  (memLp_scalarCharacter 𝕜 p F).toLp (scalarCharacter 𝕜 F)

theorem coeFn_scalarCharacterLp (p : ℝ≥0∞) (F : Finset ℕ) :
    scalarCharacterLp 𝕜 p F =ᵐ[haar] scalarCharacter 𝕜 F :=
  (memLp_scalarCharacter 𝕜 p F).coeFn_toLp

theorem inner_scalarCharacterL2 (F H : Finset ℕ) :
    inner 𝕜 (scalarCharacterLp 𝕜 2 F) (scalarCharacterLp 𝕜 2 H) =
      if F = H then 1 else 0 := by
  rw [L2.inner_def]
  calc
    (∫ x, inner 𝕜 (scalarCharacterLp 𝕜 2 F x) (scalarCharacterLp 𝕜 2 H x) ∂haar) =
        ∫ x, ((character F x * character H x : ℝ) : 𝕜) ∂haar := by
      apply integral_congr_ae
      filter_upwards [coeFn_scalarCharacterLp 𝕜 2 F, coeFn_scalarCharacterLp 𝕜 2 H] with x hx hy
      rw [hx, hy]
      simp [scalarCharacter, RCLike.inner_apply, mul_comm]
    _ = if F = H then 1 else 0 := by
      rw [integral_ofReal, integral_character_mul]
      split <;> simp

theorem orthonormal_scalarCharacterL2 : Orthonormal 𝕜 (scalarCharacterLp 𝕜 2) :=
  orthonormal_iff_ite.mpr (inner_scalarCharacterL2 𝕜)

def scalarCharacterContinuous (F : Finset ℕ) : C(Group, 𝕜) :=
  ⟨scalarCharacter 𝕜 F, continuous_scalarCharacter 𝕜 F⟩

@[simp] theorem scalarCharacterContinuous_empty : scalarCharacterContinuous 𝕜 ∅ = 1 := by
  ext x
  simp [scalarCharacterContinuous, scalarCharacter]

theorem scalarCharacterContinuous_symmDiff (F H : Finset ℕ) :
    scalarCharacterContinuous 𝕜 (F ∆ H) =
      scalarCharacterContinuous 𝕜 F * scalarCharacterContinuous 𝕜 H := by
  ext x
  exact scalarCharacter_symmDiff 𝕜 F H x

@[simp] theorem star_scalarCharacterContinuous (F : Finset ℕ) :
    star (scalarCharacterContinuous 𝕜 F) = scalarCharacterContinuous 𝕜 F := by
  ext x
  exact star_scalarCharacter 𝕜 F x

def scalarCharacterSubmonoid : Submonoid C(Group, 𝕜) where
  carrier := Set.range (scalarCharacterContinuous 𝕜)
  one_mem' := ⟨∅, scalarCharacterContinuous_empty 𝕜⟩
  mul_mem' := by
    rintro f g ⟨F, rfl⟩ ⟨H, rfl⟩
    exact ⟨F ∆ H, scalarCharacterContinuous_symmDiff 𝕜 F H⟩

theorem star_scalarCharacterSubmonoid :
    star (scalarCharacterSubmonoid 𝕜 : Set C(Group, 𝕜)) =
      (scalarCharacterSubmonoid 𝕜 : Set C(Group, 𝕜)) := by
  ext f
  change star f ∈ Set.range (scalarCharacterContinuous 𝕜) ↔
    f ∈ Set.range (scalarCharacterContinuous 𝕜)
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F, by simpa only [star_scalarCharacterContinuous, star_star] using congrArg star hF⟩
  · rintro ⟨F, rfl⟩
    exact ⟨F, (star_scalarCharacterContinuous 𝕜 F).symm⟩

/-- Finite Walsh polynomials over an RCLike field, closed under conjugation. -/
def scalarPolynomials : StarSubalgebra 𝕜 C(Group, 𝕜) :=
  StarAlgebra.adjoin 𝕜 (scalarCharacterSubmonoid 𝕜 : Set C(Group, 𝕜))

theorem scalarPolynomials_toSubmodule :
    (scalarPolynomials 𝕜).toSubmodule =
      Submodule.span 𝕜 (Set.range (scalarCharacterContinuous 𝕜)) := by
  rw [scalarPolynomials, StarAlgebra.adjoin_eq_span, star_scalarCharacterSubmonoid,
    Set.union_self, (scalarCharacterSubmonoid 𝕜).closure_eq]
  rfl

theorem scalarPolynomials_separatesPoints : (scalarPolynomials 𝕜).SeparatesPoints := by
  intro x y hxy
  have hn : ∃ j, x j ≠ y j := by
    by_contra h
    apply hxy
    funext j
    exact not_not.mp (fun hj => h ⟨j, hj⟩)
  obtain ⟨j, hj⟩ := hn
  refine ⟨scalarCharacter 𝕜 {j}, ⟨scalarCharacterContinuous 𝕜 {j}, ?_, rfl⟩, ?_⟩
  · exact StarAlgebra.subset_adjoin 𝕜 _ ⟨{j}, rfl⟩
  · intro h
    apply hj
    apply signValue_injective
    apply RCLike.ofReal_injective (K := 𝕜)
    simpa only [scalarCharacter, character_singleton] using h

theorem scalarPolynomials_dense : Dense (scalarPolynomials 𝕜 : Set C(Group, 𝕜)) := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (scalarPolynomials 𝕜) (scalarPolynomials_separatesPoints 𝕜)
  rw [SetLike.ext'_iff] at h
  change closure (scalarPolynomials 𝕜 : Set C(Group, 𝕜)) = Set.univ at h
  exact dense_iff_closure_eq.mpr h

theorem toLp_scalarCharacterContinuous (p : ℝ≥0∞) [Fact (1 ≤ p)] (F : Finset ℕ) :
    ContinuousMap.toLp p haar 𝕜 (scalarCharacterContinuous 𝕜 F) =
      scalarCharacterLp 𝕜 p F := by
  apply Lp.ext
  exact (ContinuousMap.coeFn_toLp haar (scalarCharacterContinuous 𝕜 F)).trans
    (coeFn_scalarCharacterLp 𝕜 p F).symm

/-- Walsh density, simultaneously covering the real and complex cases. -/
theorem dense_span_scalarCharacterLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense (Submodule.span 𝕜 (Set.range (scalarCharacterLp 𝕜 p)) : Set (Lp 𝕜 p haar)) := by
  apply (ContinuousMap.toLp_denseRange (p := p) 𝕜 haar 𝕜 hp).dense_of_mapsTo
    (ContinuousMap.toLp p haar 𝕜).continuous (scalarPolynomials_dense 𝕜)
  intro f hf
  have hf' : f ∈ Submodule.span 𝕜 (Set.range (scalarCharacterContinuous 𝕜)) := by
    rw [← scalarPolynomials_toSubmodule]
    exact hf
  have him := Submodule.image_span_subset_span
    (ContinuousMap.toLp p haar 𝕜).toLinearMap (Set.range (scalarCharacterContinuous 𝕜)) ⟨f, hf', rfl⟩
  have hr : (ContinuousMap.toLp p haar 𝕜) '' Set.range (scalarCharacterContinuous 𝕜) =
      Set.range (scalarCharacterLp 𝕜 p) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext (toLp_scalarCharacterContinuous 𝕜 p))
  simpa only [ContinuousLinearMap.coe_coe, hr] using him

/-- The complete Walsh Hilbert basis, over either scalar field. -/
def scalarHilbertBasis : HilbertBasis (Finset ℕ) 𝕜 (Lp 𝕜 2 haar) :=
  HilbertBasis.mk (orthonormal_scalarCharacterL2 𝕜) (by
    rw [Submodule.dense_iff_topologicalClosure_eq_top.mp
      (dense_span_scalarCharacterLp 𝕜 2 (by norm_num))])

@[simp] theorem scalarHilbertBasis_apply (F : Finset ℕ) :
    scalarHilbertBasis 𝕜 F = scalarCharacterLp 𝕜 2 F := by
  exact congrFun (HilbertBasis.coe_mk _ _) F

end Scalars

end Walsh
end PL1
