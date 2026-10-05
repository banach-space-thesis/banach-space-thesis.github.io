import ThesisCommon.Analysis.ExtendedReciprocalProfile

/-! The actual two-stage numerical regularization used in the source:
take the increasing submultiplicative hull, form x/h(x), then take its
concave envelope. All operations are defined by finite costs or convex
hulls; the desired profile properties are theorems, not object fields. -/
noncomputable section
namespace ThesisCommon

def concavifiedReciprocal (φ : ℝ → ℝ) : ℝ → ℝ :=
  positiveConcaveEnvelope (extendedReciprocalProfile (submultiplicativeHull φ))

def regularizedProfile (φ : ℝ → ℝ) (x : ℝ) : ℝ := x / concavifiedReciprocal φ x

theorem submultiplicativeHull_one {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (hφone : φ 1 ≤ 1) : submultiplicativeHull φ 1 = 1 :=
  le_antisymm ((submultiplicativeHull_le hφ le_rfl).trans hφone) (one_le_submultiplicativeHull hφ 1)

theorem concavifiedReciprocal_concaveOn {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) : ConcaveOn ℝ (Set.Ici 0) (concavifiedReciprocal φ) :=
  positiveConcaveEnvelope_concaveOn
    (fun _ hx => extendedReciprocalProfile_nonneg (fun x _ => one_le_submultiplicativeHull hφ x) hx)
    (fun _ hx => extendedReciprocalProfile_le_id (fun x _ => one_le_submultiplicativeHull hφ x) hx)

theorem concavifiedReciprocal_monotoneOn {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) : MonotoneOn (concavifiedReciprocal φ) (Set.Ici 0) :=
  positiveConcaveEnvelope_monotoneOn
    (fun _ hx => extendedReciprocalProfile_nonneg (fun x _ => one_le_submultiplicativeHull hφ x) hx)
    (fun _ hx => extendedReciprocalProfile_le_id (fun x _ => one_le_submultiplicativeHull hφ x) hx)

theorem concavifiedReciprocal_mul_le {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    concavifiedReciprocal φ x * concavifiedReciprocal φ y ≤ concavifiedReciprocal φ (x * y) :=
  positiveConcaveEnvelope_mul_le
    (fun _ hx => extendedReciprocalProfile_nonneg (fun x _ => one_le_submultiplicativeHull hφ x) hx)
    (fun _ hx => extendedReciprocalProfile_le_id (fun x _ => one_le_submultiplicativeHull hφ x) hx)
    (fun _ _ hx hy => extendedReciprocalProfile_mul_le
      (fun x _ => one_le_submultiplicativeHull hφ x) ((submultiplicativeHull_mono hφ).monotoneOn _)
      (fun _ _ hx hy => submultiplicativeHull_mul_le hφ hx hy) hx hy) hx hy

theorem concavifiedReciprocal_small {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    concavifiedReciprocal φ x = x :=
  positiveConcaveEnvelope_extendedReciprocalProfile_small
    (fun x _ => one_le_submultiplicativeHull hφ x) hx hx1

theorem concavifiedReciprocal_le_id {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) {x : ℝ} (hx : 0 ≤ x) : concavifiedReciprocal φ x ≤ x :=
  positiveConcaveEnvelope_le_id
    (fun _ hx => extendedReciprocalProfile_nonneg (fun x _ => one_le_submultiplicativeHull hφ x) hx)
    (fun _ hx => extendedReciprocalProfile_le_id (fun x _ => one_le_submultiplicativeHull hφ x) hx) hx

theorem reciprocal_hull_le_concavifiedReciprocal {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (hφone : φ 1 ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    x / submultiplicativeHull φ x ≤ concavifiedReciprocal φ x := by
  have hh := le_positiveConcaveEnvelope
    (fun _ hx => extendedReciprocalProfile_nonneg (fun x _ => one_le_submultiplicativeHull hφ x) hx)
    (fun _ hx => extendedReciprocalProfile_le_id (fun x _ => one_le_submultiplicativeHull hφ x) hx)
    (zero_le_one.trans hx)
  rwa [extendedReciprocalProfile_of_one_le (submultiplicativeHull_one hφ hφone) hx] at hh

theorem concavifiedReciprocal_pos {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (hφone : φ 1 ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    0 < concavifiedReciprocal φ x :=
  (div_pos (zero_lt_one.trans_le hx) (zero_lt_one.trans_le (one_le_submultiplicativeHull hφ x))).trans_le
    (reciprocal_hull_le_concavifiedReciprocal hφ hφone hx)

theorem one_le_regularizedProfile {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (hφone : φ 1 ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ regularizedProfile φ x := by
  rw [regularizedProfile, le_div_iff₀ (concavifiedReciprocal_pos hφ hφone hx), one_mul]
  exact concavifiedReciprocal_le_id hφ (zero_le_one.trans hx)

theorem regularizedProfile_le_hull {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (hφone : φ 1 ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    regularizedProfile φ x ≤ submultiplicativeHull φ x := by
  rw [regularizedProfile, div_le_iff₀ (concavifiedReciprocal_pos hφ hφone hx)]
  have hh := (div_le_iff₀ (zero_lt_one.trans_le (one_le_submultiplicativeHull hφ x))).mp
    (reciprocal_hull_le_concavifiedReciprocal hφ hφone hx)
  simpa only [mul_comm] using hh

theorem regularizedProfile_le {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (hφone : φ 1 ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    regularizedProfile φ x ≤ φ x :=
  (regularizedProfile_le_hull hφ hφone hx).trans (submultiplicativeHull_le hφ hx)

theorem regularizedProfile_mul_le {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (hφone : φ 1 ≤ 1) {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    regularizedProfile φ (x * y) ≤ regularizedProfile φ x * regularizedProfile φ y := by
  have hxy : 1 ≤ x * y := by nlinarith
  unfold regularizedProfile
  rw [div_mul_div_comm]
  exact div_le_div_of_nonneg_left (zero_le_one.trans hxy)
    (mul_pos (concavifiedReciprocal_pos hφ hφone hx) (concavifiedReciprocal_pos hφ hφone hy))
    (concavifiedReciprocal_mul_le hφ (zero_le_one.trans hx) (zero_le_one.trans hy))

end ThesisCommon
