import ThesisCommon.Analysis.GowersMaureySpreadProperness
import Mathlib.Order.Filter.Cofinite

/-! Explicit finite-square exhaustion of the actual tail-spread family.
For finitely supported coefficients and vectors the pairing vanishes
outside a finite square; in particular it obeys the coordinate-maximum
estimate needed before source Lemma 8. No assertion about arbitrary
completed-space dual functionals is made here. -/
noncomputable section
open Filter
open scoped NNReal
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def finiteCoordinateMaximum (x : C00 𝕜) : ℝ :=
  (x.support.sup (fun i => ‖x i‖₊) : ℝ≥0)

theorem finiteCoordinateMaximum_nonneg (x : C00 𝕜) : 0 ≤ finiteCoordinateMaximum x :=
  NNReal.coe_nonneg _

theorem norm_coordinate_le_finiteCoordinateMaximum (x : C00 𝕜) (i : ℕ) :
    ‖x i‖ ≤ finiteCoordinateMaximum x := by
  classical
  by_cases hi : i ∈ x.support
  · dsimp only [finiteCoordinateMaximum]
    exact_mod_cast (Finset.le_sup (f := fun j => ‖x j‖₊) hi)
  · rw [Finsupp.notMem_support_iff.mp hi, norm_zero]
    exact finiteCoordinateMaximum_nonneg x

def spreadParameterSquare (r : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (r+1)).product (Finset.range (r+1))

@[simp] theorem mem_spreadParameterSquare (m n r : ℕ) :
    (m,n) ∈ spreadParameterSquare r ↔ m ≤ r ∧ n ≤ r := by
  simp [spreadParameterSquare, Nat.lt_succ_iff]

theorem spreadParameterSquare_mono : Monotone spreadParameterSquare := by
  intro r s hrs z hz
  rcases z with ⟨m,n⟩
  exact (mem_spreadParameterSquare m n s).mpr
    ⟨((mem_spreadParameterSquare m n r).mp hz).1.trans hrs,
      ((mem_spreadParameterSquare m n r).mp hz).2.trans hrs⟩

theorem spreadParameterSquare_exhausts (z : ℕ × ℕ) :
    ∃ r, z ∈ spreadParameterSquare r :=
  ⟨max z.1 z.2, (mem_spreadParameterSquare _ _ _).mpr
    ⟨le_max_left _ _, le_max_right _ _⟩⟩

def tailSpreadSquare (𝕜 : Type*) [RCLike 𝕜] (r : ℕ) :
    Finset (C00 𝕜 →ₗ[𝕜] C00 𝕜) := by
  classical
  exact (spreadParameterSquare r).image (fun z => spread z.1 z.2)

theorem tailSpreadSquare_mono : Monotone (tailSpreadSquare 𝕜) := by
  classical
  intro r s hrs
  exact Finset.image_mono (fun z : ℕ × ℕ => spread (𝕜 := 𝕜) z.1 z.2)
    (spreadParameterSquare_mono hrs)

theorem tailSpreadSquare_exhausts (S : C00 𝕜 →ₗ[𝕜] C00 𝕜) :
    S ∈ tailSpreadFamily 𝕜 ↔ ∃ r, S ∈ tailSpreadSquare 𝕜 r := by
  classical
  constructor
  · rintro ⟨z,rfl⟩
    obtain ⟨r,hr⟩ := spreadParameterSquare_exhausts z
    exact ⟨r, Finset.mem_image.mpr ⟨z,hr,rfl⟩⟩
  · rintro ⟨r,hr⟩
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨z,rfl⟩

theorem spread_eq_zero_of_support_before (m n : ℕ) (x : C00 𝕜)
    (hx : ∀ i ∈ x.support, i < m) : spread m n x = 0 := by
  ext i
  rw [spread_apply]
  split_ifs with hn
  · have hi : i-n+m ∉ x.support := by
      intro h
      have hh := hx _ h
      omega
    exact Finsupp.notMem_support_iff.mp hi
  · rfl

theorem pairing_spread_eq_zero_outside_square (a x : C00 𝕜) (r m n : ℕ)
    (ha : ∀ i ∈ a.support, i ≤ r) (hx : ∀ i ∈ x.support, i ≤ r)
    (houtside : (m,n) ∉ spreadParameterSquare r) :
    pairing a (spread m n x) = 0 := by
  by_cases hm : m ≤ r
  · have hn : r < n := by
      have h := mt (mem_spreadParameterSquare m n r).mpr houtside
      omega
    rw [← pairing_spread_left n m,
      spread_eq_zero_of_support_before n m a (fun i hi => (ha i hi).trans_lt hn)]
    simp [pairing, Finsupp.sum]
  · rw [spread_eq_zero_of_support_before m n x (fun i hi => by have h := hx i hi; omega), map_zero]

def pairingSpreadCutoff (a x : C00 𝕜) : ℕ :=
  max (a.support.sup id) (x.support.sup id)

theorem pairing_spread_eq_zero_of_cutoff (a x : C00 𝕜) {r : ℕ}
    (hr : pairingSpreadCutoff a x ≤ r) (m n : ℕ)
    (houtside : (m,n) ∉ spreadParameterSquare r) :
    pairing a (spread m n x) = 0 := by
  apply pairing_spread_eq_zero_outside_square a x r m n ?_ ?_ houtside
  · intro i hi
    exact (Finset.le_sup (f := id) hi).trans ((le_max_left _ _).trans hr)
  · intro i hi
    exact (Finset.le_sup (f := id) hi).trans ((le_max_right _ _).trans hr)

theorem pairing_tailSpreadSquare_compl_eq_zero (a x : C00 𝕜) {r : ℕ}
    (hr : pairingSpreadCutoff a x ≤ r) {S : C00 𝕜 →ₗ[𝕜] C00 𝕜}
    (hS : S ∈ tailSpreadFamily 𝕜) (hout : S ∉ tailSpreadSquare 𝕜 r) :
    pairing a (S x) = 0 := by
  classical
  obtain ⟨⟨m,n⟩,rfl⟩ := hS
  apply pairing_spread_eq_zero_of_cutoff a x hr m n
  intro h
  exact hout (Finset.mem_image.mpr ⟨(m,n),h,rfl⟩)

theorem pairing_spread_norm_le_coordinateMaximum_outside_square (a x : C00 𝕜)
    {r : ℕ} (hr : pairingSpreadCutoff a x ≤ r) (m n : ℕ)
    (houtside : (m,n) ∉ spreadParameterSquare r) :
    ‖pairing a (spread m n x)‖ ≤ finiteCoordinateMaximum a * finiteCoordinateMaximum x := by
  rw [pairing_spread_eq_zero_of_cutoff a x hr m n houtside, norm_zero]
  exact mul_nonneg (finiteCoordinateMaximum_nonneg a) (finiteCoordinateMaximum_nonneg x)

theorem eventually_pairing_spread_eq_zero (a x : C00 𝕜) :
    ∀ᶠ z : ℕ × ℕ in cofinite, pairing a (spread z.1 z.2 x) = 0 := by
  filter_upwards [(spreadParameterSquare (pairingSpreadCutoff a x)).eventually_cofinite_notMem]
    with z hz
  exact pairing_spread_eq_zero_of_cutoff a x le_rfl z.1 z.2 hz

theorem eventually_pairing_spread_norm_le_coordinateMaximum (a x : C00 𝕜) :
    ∀ᶠ z : ℕ × ℕ in cofinite,
      ‖pairing a (spread z.1 z.2 x)‖ ≤ finiteCoordinateMaximum a * finiteCoordinateMaximum x := by
  filter_upwards [eventually_pairing_spread_eq_zero a x] with z hz
  rw [hz, norm_zero]
  exact mul_nonneg (finiteCoordinateMaximum_nonneg a) (finiteCoordinateMaximum_nonneg x)

end ThesisCommon.GowersMaurey
