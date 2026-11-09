import LindenstraussRetraction.AnisotropicBidual
import LindenstraussRetraction.QuotientLemmas
import LindenstraussRetraction.Correction

/-! # A coordinate retraction produces an approximate quotient section -/

noncomputable section

open Filter Topology

namespace LindenstraussRetraction

universe u v w s

variable {𝕜 : Type s} [RCLike 𝕜]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {W : Type v} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

local instance obstructionAnisotropicNormedSpace (Q : Y →L[𝕜] W) (ε : ℝ) :
    NormedSpace 𝕜 (AnisotropicSpace Q ε) :=
  Submodule.normedSpace (𝕜 := 𝕜) (R := 𝕜) (E := Y × W) (AnisotropicSpace Q ε)

local instance obstructionBidualNormedGroup (X : Type w)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : NormedAddCommGroup (Bidual 𝕜 X) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := StrongDual 𝕜 X) (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)

/-- A contractive bidual lift stays in the anisotropic bidual ball whenever
`ε ≤ 1` and its quotient is the canonical copy of the original vector. -/
theorem norm_renormedBidualLift_le (Q : Y →L[𝕜] W) (S : W →L[𝕜] Bidual 𝕜 Y)
    (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (hQS : ∀ x, bidualMap Q (S x) = bidualEmbedding 𝕜 W x)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (x : W) :
    ‖bidualMap (toAnisotropic Q ε) (S x)‖ ≤ ‖x‖ := by
  rw [norm_bidual_toAnisotropic Q hε, hQS, (bidualEmbedding 𝕜 W).norm_map]
  apply max_le _ le_rfl
  calc
    ε * ‖S x‖ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_left (hS x) hε
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hε1 (norm_nonneg x)
    _ = ‖x‖ := one_mul _

def sphereRenormedBidualLift (Q : Y →L[𝕜] W) (S : W →L[𝕜] Bidual 𝕜 Y)
    (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (hQS : ∀ x, bidualMap Q (S x) = bidualEmbedding 𝕜 W x)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    UnitSphere W → UnitBall (Bidual 𝕜 (AnisotropicSpace Q ε)) := fun x =>
  ⟨bidualMap (toAnisotropic Q ε) (S x.val),
    (norm_renormedBidualLift_le Q S hS hQS hε hε1 x.val).trans_eq x.property⟩

theorem sphereRenormedBidualLift_uniformContinuous
    (Q : Y →L[𝕜] W) (S : W →L[𝕜] Bidual 𝕜 Y)
    (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (hQS : ∀ x, bidualMap Q (S x) = bidualEmbedding 𝕜 W x)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    UniformContinuous (sphereRenormedBidualLift Q S hS hQS hε hε1) := by
  let M : W →L[𝕜] Bidual 𝕜 (AnisotropicSpace Q ε) :=
    (bidualMap (toAnisotropic Q ε)).comp S
  exact (M.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _

/-- Comparing the lifted sphere point with any genuine lift of norm below
two gives the quantitative bidual distance below `3ε`. -/
theorem renormedBidualLift_close (Q : Y →L[𝕜] W) (S : W →L[𝕜] Bidual 𝕜 Y)
    (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (hQS : ∀ x, bidualMap Q (S x) = bidualEmbedding 𝕜 W x)
    {ε : ℝ} (hε : 0 < ε) (x : UnitSphere W) (y : Y)
    (hy : Q y = x.val) (hynorm : ‖y‖ < 2) :
    ‖bidualMap (toAnisotropic Q ε) (S x.val) -
      bidualEmbedding 𝕜 (AnisotropicSpace Q ε) (toAnisotropic Q ε y)‖ < 3 * ε := by
  have hker : bidualMap Q (S x.val - bidualEmbedding 𝕜 Y y) = 0 := by
    rw [(bidualMap Q).map_sub, hQS, bidualMap_embedding, hy, sub_self]
  rw [← bidualMap_embedding, ← (bidualMap (toAnisotropic Q ε)).map_sub,
    norm_bidual_toAnisotropic_of_ker Q hε.le _ hker]
  have hnorm : ‖S x.val - bidualEmbedding 𝕜 Y y‖ < 3 := by
    calc
      ‖S x.val - bidualEmbedding 𝕜 Y y‖ ≤ ‖S x.val‖ + ‖bidualEmbedding 𝕜 Y y‖ :=
        norm_sub_le _ _
      _ ≤ ‖x.val‖ + ‖y‖ := add_le_add (hS x.val) (le_of_eq ((bidualEmbedding 𝕜 Y).norm_map y))
      _ < 3 := by rw [x.property]; linarith
  nlinarith

/-- A ball retraction with modulus `δ` at error `a` yields a bounded uniformly
continuous approximate section whenever `3ε < δ`. -/
theorem exists_sphereApproximation_of_renormedRetraction
    (Q : Y →L[𝕜] W) (hQ : IsNormQuotient Q)
    (S : W →L[𝕜] Bidual 𝕜 Y) (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (hQS : ∀ x, bidualMap Q (S x) = bidualEmbedding 𝕜 W x)
    {ε δ a : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hδε : 3 * ε < δ)
    (R : UnitBall (Bidual 𝕜 (AnisotropicSpace Q ε)) → UnitBall (AnisotropicSpace Q ε))
    (hR : UniformContinuous R) (hfix : IsRetraction (unitBallBidualEmbedding 𝕜 _) R)
    (hmod : ∀ z z', dist z z' < δ → dist (R z) (R z') < a) :
    ∃ φ : UnitSphere W → Y, UniformContinuous φ ∧
      (∀ x, ‖φ x‖ ≤ ε⁻¹) ∧ (∀ x, ‖Q (φ x) - x.val‖ < a) := by
  have hε1 : ε ≤ 1 := by linarith
  let L := sphereRenormedBidualLift Q S hS hQS hε.le hε1
  let φ : UnitSphere W → Y := fun x => fromAnisotropic Q ε (R (L x)).val
  have hφ : UniformContinuous φ :=
    (fromAnisotropic Q ε).uniformContinuous.comp
      (uniformContinuous_subtype_val.comp
        (hR.comp (sphereRenormedBidualLift_uniformContinuous Q S hS hQS hε.le hε1)))
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro x
    exact (norm_fromAnisotropic_le Q hε (R (L x)).val).trans
      ((mul_le_mul_of_nonneg_left (R (L x)).property (inv_nonneg.mpr hε.le)).trans_eq
        (mul_one _))
  · intro x
    obtain ⟨y, hy, hynorm⟩ := hQ.exists_sphere_lift x (δ := 1) zero_lt_one
    have hy2 : ‖y‖ < 2 := by linarith
    have hyn : ‖toAnisotropic Q ε y‖ ≤ 1 := by
      rw [norm_toAnisotropic Q hε.le, hy, x.property]
      apply max_le _ le_rfl
      nlinarith
    let yb : UnitBall (AnisotropicSpace Q ε) := ⟨toAnisotropic Q ε y, hyn⟩
    have hclose : dist (L x) (unitBallBidualEmbedding 𝕜 _ yb) < δ := by
      change dist (bidualMap (toAnisotropic Q ε) (S x.val))
        (bidualEmbedding 𝕜 (AnisotropicSpace Q ε) (toAnisotropic Q ε y)) < δ
      rw [dist_eq_norm]
      exact (renormedBidualLift_close Q S hS hQS hε x y hy hy2).trans hδε
    have herror := hmod (L x) (unitBallBidualEmbedding 𝕜 _ yb) hclose
    rw [hfix yb] at herror
    change dist (R (L x)).val (toAnisotropic Q ε y) < a at herror
    rw [dist_eq_norm] at herror
    change ‖Q (fromAnisotropic Q ε (R (L x)).val) - x.val‖ < a
    rw [quotient_fromAnisotropic Q hε, ← hy,
      ← anisotropicQuotient_toAnisotropic Q ε y, ← map_sub]
    exact (anisotropicQuotient_norm_le Q ε _).trans_lt herror

/-- Renormed coordinate retractions cannot share one uniform-continuity
modulus when the quotient has no uniform section and the scales tend to zero.
This is the quantitative contradiction in Proposition `prop:auxiliary-space`.
-/
theorem no_commonRenormedBallRetractions [CompleteSpace Y] [CompleteSpace W]
    (Q : Y →L[𝕜] W) (hQ : IsNormQuotient Q) (hNoSection : ¬ HasUniformSectionOnUnitBall Q)
    (S : W →L[𝕜] Bidual 𝕜 Y) (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (hQS : ∀ x, bidualMap Q (S x) = bidualEmbedding 𝕜 W x)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε2 : ∀ n, ε n ≤ 1 / 2)
    (hlim : Tendsto ε atTop (𝓝 0))
    (R : ∀ n, UnitBall (Bidual 𝕜 (AnisotropicSpace Q (ε n))) →
      UnitBall (AnisotropicSpace Q (ε n)))
    (hR : ∀ n, UniformContinuous (R n))
    (hfix : ∀ n, IsRetraction (unitBallBidualEmbedding 𝕜 _) (R n))
    (hmod : ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧
      ∀ n z z', dist z z' < δ → dist (R n z) (R n z') < a) : False := by
  obtain ⟨δ, hδ, hδmod⟩ := hmod (1 / 2) (by norm_num)
  have hscale : Tendsto (fun n => 3 * ε n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  obtain ⟨n, hn⟩ := (hscale.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨φ, hφ, hbound, herror⟩ := exists_sphereApproximation_of_renormedRetraction
    Q hQ S hS hQS (hε n) (hε2 n) hn (R n) (hR n) (hfix n) (hδmod n)
  apply hNoSection
  exact correction (E := Y) (W := W) Q hQ φ hφ
    ⟨(ε n)⁻¹, inv_nonneg.mpr (hε n).le, hbound⟩
    (1 / 2) (by norm_num) (by norm_num) (fun x => (herror x).le)

end LindenstraussRetraction
