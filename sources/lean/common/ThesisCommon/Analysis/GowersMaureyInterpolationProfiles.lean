import ThesisCommon.Analysis.RegularizedProfileBarriers
import ThesisCommon.Analysis.ConcaveIdentityExtension
import ThesisCommon.Analysis.GowersMaureyLogSubmultiplicative

/-! The source's actual numerical interpolation construction, for any
selected set of natural sizes. This file defines the seed and both hulls,
and verifies properties that do not require the separation of the sizes.
The equality with f on the large gaps is a separate, still needed step. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

def interpolationSeed (K : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ (fun k : ℕ => (k : ℝ)) '' K then Real.sqrt (logarithmicWeight x) else logarithmicWeight x

def interpolationG (K : Set ℕ) : ℝ → ℝ := concavifiedReciprocal (interpolationSeed K)

def interpolationProfile (K : Set ℕ) : ℝ → ℝ := regularizedProfile (interpolationSeed K)

theorem one_le_logarithmicWeight_real {x : ℝ} (hx : 1 ≤ x) : 1 ≤ logarithmicWeight x := by
  have hh := logarithmicWeight_strictMonoOn.monotoneOn (by norm_num : (1 : ℝ) ∈ Set.Ici 1) hx hx
  simpa only [logarithmicWeight_one] using hh

theorem logarithmicWeight_le_self_real {x : ℝ} (hx : 1 ≤ x) : logarithmicWeight x ≤ x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [logarithmicWeight_one]
  · exact (logarithmicWeight_lt_self hx).le

theorem one_le_sqrt_logarithmicWeight {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ Real.sqrt (logarithmicWeight x) := by
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (one_le_logarithmicWeight_real hx)

theorem sqrt_logarithmicWeight_le_weight {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt (logarithmicWeight x) ≤ logarithmicWeight x := by
  have hf := one_le_logarithmicWeight_real hx
  have hs := Real.sq_sqrt (zero_le_one.trans hf)
  have hp := one_le_sqrt_logarithmicWeight hx
  nlinarith

theorem interpolationSeed_bounds (K : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt (logarithmicWeight x) ≤ interpolationSeed K x ∧
      interpolationSeed K x ≤ logarithmicWeight x := by
  unfold interpolationSeed
  split_ifs
  · exact ⟨le_rfl, sqrt_logarithmicWeight_le_weight hx⟩
  · exact ⟨sqrt_logarithmicWeight_le_weight hx, le_rfl⟩

theorem interpolationSeed_ge_one (K : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ interpolationSeed K x := (one_le_sqrt_logarithmicWeight hx).trans (interpolationSeed_bounds K hx).1

theorem interpolationSeed_one (K : Set ℕ) : interpolationSeed K 1 = 1 := by
  unfold interpolationSeed
  simp [logarithmicWeight_one]

theorem interpolationG_concaveOn (K : Set ℕ) : ConcaveOn ℝ (Set.Ici 0) (interpolationG K) :=
  concavifiedReciprocal_concaveOn (fun _ hx => interpolationSeed_ge_one K hx)

theorem interpolationG_monotoneOn (K : Set ℕ) : MonotoneOn (interpolationG K) (Set.Ici 0) :=
  concavifiedReciprocal_monotoneOn (fun _ hx => interpolationSeed_ge_one K hx)

theorem interpolationG_small (K : Set ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    interpolationG K x = x := concavifiedReciprocal_small (fun _ ht => interpolationSeed_ge_one K ht) hx hx1

theorem interpolationG_mul_le (K : Set ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    interpolationG K x * interpolationG K y ≤ interpolationG K (x * y) :=
  concavifiedReciprocal_mul_le (fun _ ht => interpolationSeed_ge_one K ht) hx hy

theorem interpolationProfile_le_weight (K : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    interpolationProfile K x ≤ logarithmicWeight x :=
  (regularizedProfile_le (fun _ ht => interpolationSeed_ge_one K ht)
    (interpolationSeed_one K).le hx).trans (interpolationSeed_bounds K hx).2

theorem interpolationProfile_inverse_mul (K : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (interpolationProfile K x)⁻¹ * x = interpolationG K x :=
  regularizedProfile_inverse_mul (fun _ ht => interpolationSeed_ge_one K ht)
    (interpolationSeed_one K).le hx

theorem interpolationProfile_le_sqrt_at_selected_size (K : Set ℕ) {k : ℕ}
    (hk : 0 < k) (hK : k ∈ K) :
    interpolationProfile K k ≤ Real.sqrt (logarithmicWeight k) := by
  have hh := regularizedProfile_le (fun _ ht => interpolationSeed_ge_one K ht)
    (interpolationSeed_one K).le (show (1 : ℝ) ≤ k by exact_mod_cast hk)
  change interpolationProfile K k ≤ interpolationSeed K k at hh
  simpa only [interpolationSeed, if_pos (show (k : ℝ) ∈ (fun j : ℕ => (j : ℝ)) '' K from ⟨k, hK, rfl⟩)] using hh

end ThesisCommon.GowersMaurey
