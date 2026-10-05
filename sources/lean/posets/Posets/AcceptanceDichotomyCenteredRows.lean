import Posets.AcceptanceDichotomyIndicatorTest
import Posets.AcceptanceDichotomyRejectionTransfer

/-! Convert centered row oscillation into a disjoint rejecting restriction. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

def summableScalarRow (f : ℕ → 𝕜) (hf : Summable (fun i => ‖f i‖)) :
    lp (fun _ : ℕ => 𝕜) 1 :=
  ⟨f, memℓp_gen (by simpa using hf)⟩

theorem exists_disjoint_rejection_of_centered_rows (M : ScalarMatrix 𝕜)
    (hM : HasBoundedRows 𝕜 M) (A : Set ℕ)
    (hsupport : ∀ k i, i ∉ A → M k i = 0)
    (k : ℕ → ℕ) (hk : StrictMono k) (hkA : ∀ n, k n ∈ A)
    (b : ℕ → 𝕜) (hb : Summable (fun i => ‖b i‖))
    (hcol : ∀ i, Tendsto (fun n => M (k n) i) atTop (𝓝 (b i)))
    (hdiag : Tendsto (fun n => M (k n) (k n)) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) (hmass : ∀ n, δ ≤ ∑' i, ‖M (k n) i - b i‖) :
    ∃ B D : Set ℕ, B ⊆ A ∧ D ⊆ A ∧ Disjoint B D ∧ Rejects 𝕜 B D M := by
  let rows (n : ℕ) := summableScalarRow (M (k n)) (hM.1 (k n))
  let brow := summableScalarRow b hb
  let u (n : ℕ) := rows n - brow
  have hu (i : ℕ) : Tendsto (fun n => u n i) atTop (𝓝 0) := by
    simpa [u, rows, brow, summableScalarRow] using (hcol i).sub_const (b i)
  have hbzero : Tendsto b atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hb.tendsto_atTop_zero
  have hud : Tendsto (fun n => u n (k n)) atTop (𝓝 0) := by
    simpa [u, rows, brow, summableScalarRow] using hdiag.sub (hbzero.comp hk.tendsto_atTop)
  have humass (n : ℕ) : δ ≤ ‖u n‖ := by
    rw [ThesisCommon.ellOne_norm_eq_tsum]
    exact hmass n
  obtain ⟨r, hr, C, havoid, hbad⟩ := exists_nonconvergent_indicator_test u hu k hk hud hδ humass
  let B := C ∩ A
  let D := Set.range (fun n => k (r n))
  have hD : D ⊆ A := by rintro _ ⟨n, rfl⟩; exact hkA (r n)
  have hBD : Disjoint B D := by
    apply Set.disjoint_left.mpr
    rintro i hi ⟨n, rfl⟩
    exact havoid n hi.1
  refine ⟨B, D, Set.inter_subset_right, hD, hBD, ?_⟩
  rintro ⟨a, ha⟩
  have hkD : Tendsto (fun n => k (r n)) atTop (Along D) := by
    rw [Along, Nat.cofinite_eq_atTop]
    exact tendsto_inf.mpr ⟨(hk.comp hr).tendsto_atTop,
      tendsto_principal.mpr (Eventually.of_forall (fun n => ⟨n, rfl⟩))⟩
  have hbC : ∀ i, ‖indicator 𝕜 C i‖ ≤ 1 := by
    intro i; by_cases hi : i ∈ C <;> simp [indicator, hi]
  let φ := ThesisCommon.scalarEllOneTest (indicator 𝕜 C) hbC
  have heq (n : ℕ) : φ (u (r n)) = matrixAction 𝕜 M (indicator 𝕜 B) (k (r n)) - φ brow := by
    rw [show u (r n) = rows (r n) - brow from rfl, map_sub]
    congr 1
    change (∑' i, indicator 𝕜 C i * M (k (r n)) i) =
      ∑' i, M (k (r n)) i * indicator 𝕜 B i
    apply tsum_congr
    intro i
    by_cases hi : i ∈ A
    · by_cases hiC : i ∈ C <;> simp [indicator, B, hi, hiC]
    · simp [hsupport _ _ hi]
  apply hbad
  refine ⟨a - φ brow, ((ha.comp hkD).sub_const (φ brow)).congr (fun n => ?_)⟩
  exact (heq n).symm

end Posets
