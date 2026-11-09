import BanachIsometric.EilenbergZilberTensorEvaluation
import BanachIsometric.RawTensorAddCommGroup

/-! A homotopy identity tested on the actual universal simplex pairs
extends to the homogeneous tensor complex by naturality and linearity. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW
open scoped TensorProduct

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def tensorModelDifference {n p q : ℕ} (h : p + q = n) :
    rawTensorTotalDegree (Simplex p) (Simplex q) n :=
  rawTensorComposite n (universalTensorHomogeneousGenerator h) - universalTensorHomogeneousGenerator h

def tensorModelHomotopyCandidate {n p q : ℕ} (K : UniversalTensorHomotopies n)
    (h : p + q = n + 1) : rawTensorTotalDegree (Simplex p) (Simplex q) (n + 1) :=
  tensorModelDifference h - universalTensorHomotopyEvaluation K
    (rawTensorBoundary (Simplex p) (Simplex q) n (universalTensorHomogeneousGenerator h))

theorem tensorHomotopy_zero_of_model {K : UniversalTensorHomotopies 0}
    (hK : ∀ p q (h : p + q = 0), rawTensorBoundary (Simplex p) (Simplex q) 0 (K p q h) =
      tensorModelDifference h) (c : rawTensorTotalDegree X Y 0) :
    rawTensorBoundary X Y 0 (universalTensorHomotopyEvaluation K c) = rawTensorComposite 0 c - c := by
  have he : (rawTensorBoundary X Y 0).comp (universalTensorHomotopyEvaluation K) =
      rawTensorComposite 0 - LinearMap.id := by
    apply rawTensorHomogeneous_linearMap_ext
    intro p q hpq σ τ
    let d := rawTensorHomogeneousInclusion hpq (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1)
    change rawTensorBoundary X Y 0 (universalTensorHomotopyEvaluation K d) =
      rawTensorComposite 0 d - d
    have hgen : rawBigradedTensorMapHomogeneous σ τ 0 (universalTensorHomogeneousGenerator hpq) = d :=
      universalTensorHomogeneousGenerator_pushforward hpq σ τ
    rw [← hgen, universalTensorHomotopyEvaluation_naturality,
      universalTensorHomotopyEvaluation_generator, rawTensorComposite_naturality, ← map_sub]
    exact (LinearMap.congr_fun (rawBigradedTensorMapHomogeneous_boundary σ τ 0) _).trans
      (congrArg (rawBigradedTensorMapHomogeneous σ τ 0) (hK p q hpq))
  exact LinearMap.congr_fun he c

theorem tensorHomotopy_succ_of_model {n : ℕ} {K : UniversalTensorHomotopies n}
    {L : UniversalTensorHomotopies (n + 1)}
    (hL : ∀ p q (h : p + q = n + 1), rawTensorBoundary (Simplex p) (Simplex q) (n + 1) (L p q h) =
      tensorModelHomotopyCandidate K h) (c : rawTensorTotalDegree X Y (n + 1)) :
    rawTensorBoundary X Y (n + 1) (universalTensorHomotopyEvaluation L c) =
      rawTensorComposite (n + 1) c - c - universalTensorHomotopyEvaluation K (rawTensorBoundary X Y n c) := by
  have he : (rawTensorBoundary X Y (n + 1)).comp (universalTensorHomotopyEvaluation L) =
      rawTensorComposite (n + 1) - LinearMap.id -
        (universalTensorHomotopyEvaluation K).comp (rawTensorBoundary X Y n) := by
    apply rawTensorHomogeneous_linearMap_ext
    intro p q hpq σ τ
    let d := rawTensorHomogeneousInclusion hpq (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1)
    change rawTensorBoundary X Y (n + 1) (universalTensorHomotopyEvaluation L d) =
      rawTensorComposite (n + 1) d - d -
        universalTensorHomotopyEvaluation K (rawTensorBoundary X Y n d)
    have hgen : rawBigradedTensorMapHomogeneous σ τ (n + 1) (universalTensorHomogeneousGenerator hpq) = d :=
      universalTensorHomogeneousGenerator_pushforward hpq σ τ
    have hb := LinearMap.congr_fun (rawBigradedTensorMapHomogeneous_boundary σ τ n)
      (universalTensorHomogeneousGenerator hpq)
    simp only [LinearMap.comp_apply] at hb
    rw [← hgen, universalTensorHomotopyEvaluation_naturality,
      universalTensorHomotopyEvaluation_generator, rawTensorComposite_naturality, hb,
      universalTensorHomotopyEvaluation_naturality, ← map_sub, ← map_sub]
    exact (LinearMap.congr_fun (rawBigradedTensorMapHomogeneous_boundary σ τ (n + 1)) _).trans
      (congrArg (rawBigradedTensorMapHomogeneous σ τ (n + 1)) (hL p q hpq))
  exact LinearMap.congr_fun he c

end BanachIsometric.SingularEZ
