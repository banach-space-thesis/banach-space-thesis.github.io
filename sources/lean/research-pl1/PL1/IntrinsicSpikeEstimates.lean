import PL1.IntrinsicGraph

/-!
# Summable coordinate estimates for actual intrinsic products

The multiplication map is an actual continuous linear operator on the base
space. Coordinate norm identities and commutator estimates remain explicit
inputs here; the conclusions concern the original intrinsic graph and norm.
-/

noncomputable section
open scoped BigOperators

namespace PL1.IntrinsicSpikeEstimates
open IntrinsicGraph

variable {𝕜 Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {D : ℕ → Y →L[𝕜] Y}

theorem summable_norm_coord (f : Space D) : Summable (fun n => ‖coord D n f‖) := by
  simpa only [coord_apply, ENNReal.toReal_one, Real.rpow_one] using
    (lp.memℓp (f : Ambient (Y := Y))).summable (by norm_num)

theorem summable_product_coordinates (M : Y →L[𝕜] Y) (f : Space D)
    (e : ℕ → ℝ) (he : Summable e)
    (hpres : ∀ n, ‖M (coord D n f)‖ = ‖coord D n f‖)
    (hcomm : ∀ n, ‖D n (M (evalZero D f)) - M (coord D n f)‖ ≤ e n) :
    Summable (fun n => ‖D n (M (evalZero D f))‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => ?_) ((summable_norm_coord f).add he)
  calc
    ‖D n (M (evalZero D f))‖ ≤
        ‖D n (M (evalZero D f)) - M (coord D n f)‖ + ‖M (coord D n f)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ e n + ‖coord D n f‖ := by rw [hpres]; exact add_le_add (hcomm n) le_rfl
    _ = ‖coord D n f‖ + e n := add_comm _ _

theorem norm_product_sub_norm_le (M : Y →L[𝕜] Y) (f g : Space D)
    (hg : evalZero D g = M (evalZero D f)) (e : ℕ → ℝ) (he : Summable e)
    (hpres : ∀ n, ‖M (coord D n f)‖ = ‖coord D n f‖)
    (hcomm : ∀ n, ‖D n (M (evalZero D f)) - M (coord D n f)‖ ≤ e n) :
    |‖g‖ - ‖f‖| ≤ ∑' n, e n := by
  have hcoord (n : ℕ) : ‖coord D n g - M (coord D n f)‖ ≤ e n := by
    rw [coord_eq, hg]
    exact hcomm n
  have hupper : ‖g‖ ≤ ‖f‖ + ∑' n, e n := by
    rw [norm_eq_tsum, norm_eq_tsum, ← (summable_norm_coord f).tsum_add he]
    apply (summable_norm_coord g).tsum_le_tsum _ ((summable_norm_coord f).add he)
    intro n
    calc
      ‖coord D n g‖ ≤ ‖coord D n g - M (coord D n f)‖ + ‖M (coord D n f)‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ ‖coord D n f‖ + e n := by rw [hpres]; linarith [hcoord n]
  have hlower : ‖f‖ ≤ ‖g‖ + ∑' n, e n := by
    rw [norm_eq_tsum, norm_eq_tsum, ← (summable_norm_coord g).tsum_add he]
    apply (summable_norm_coord f).tsum_le_tsum _ ((summable_norm_coord g).add he)
    intro n
    calc
      ‖coord D n f‖ = ‖M (coord D n f)‖ := (hpres n).symm
      _ ≤ ‖M (coord D n f) - coord D n g‖ + ‖coord D n g‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ ‖coord D n g‖ + e n := by rw [norm_sub_rev]; linarith [hcoord n]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Norm summability constructs the product in the actual graph, not in a new
space with a modified norm. -/
theorem exists_product (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
    (M : Y →L[𝕜] Y) (f : Space D) (e : ℕ → ℝ) (he : Summable e)
    (hpres : ∀ n, ‖M (coord D n f)‖ = ‖coord D n f‖)
    (hcomm : ∀ n, ‖D n (M (evalZero D f)) - M (coord D n f)‖ ≤ e n) :
    ∃ g : Space D, evalZero D g = M (evalZero D f) ∧ |‖g‖ - ‖f‖| ≤ ∑' n, e n := by
  let g := ofSummable D h0 (M (evalZero D f))
    (summable_product_coordinates M f e he hpres hcomm)
  have hg : evalZero D g = M (evalZero D f) := evalZero_ofSummable D h0 _ _
  exact ⟨g, hg, norm_product_sub_norm_le M f g hg e he hpres hcomm⟩

/-- Coordinatewise separation survives the summable commutator error. -/
theorem separation (M : Y →L[𝕜] Y) (h f g : Space D)
    (hg : evalZero D g = M (evalZero D f)) (e : ℕ → ℝ) (he : Summable e)
    (c : ℝ)
    (hsep : ∀ n, c * (‖coord D n h‖ + ‖coord D n f‖) ≤
      ‖coord D n h + M (coord D n f)‖)
    (hcomm : ∀ n, ‖D n (M (evalZero D f)) - M (coord D n f)‖ ≤ e n) :
    c * (‖h‖ + ‖f‖) - (∑' n, e n) ≤ ‖h + g‖ := by
  have hbound (n : ℕ) : c * (‖coord D n h‖ + ‖coord D n f‖) ≤
      ‖coord D n (h + g)‖ + e n := by
    have heq : coord D n h + M (coord D n f) =
        coord D n (h + g) - (coord D n g - M (coord D n f)) := by
      rw [map_add]
      abel
    have herr : ‖coord D n g - M (coord D n f)‖ ≤ e n := by
      rw [coord_eq, hg]
      exact hcomm n
    calc
      _ ≤ ‖coord D n h + M (coord D n f)‖ := hsep n
      _ = ‖coord D n (h + g) - (coord D n g - M (coord D n f))‖ := by rw [heq]
      _ ≤ ‖coord D n (h + g)‖ + ‖coord D n g - M (coord D n f)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl herr
  have hs := (((summable_norm_coord h).add (summable_norm_coord f)).mul_left c).tsum_le_tsum
    hbound ((summable_norm_coord (h + g)).add he)
  rw [tsum_mul_left, (summable_norm_coord h).tsum_add (summable_norm_coord f),
    (summable_norm_coord (h + g)).tsum_add he, ← norm_eq_tsum, ← norm_eq_tsum,
    ← norm_eq_tsum] at hs
  linarith

end PL1.IntrinsicSpikeEstimates
