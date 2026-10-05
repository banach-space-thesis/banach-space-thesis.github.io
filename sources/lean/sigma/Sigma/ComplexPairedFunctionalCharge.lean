import Sigma.ComplexPairedCoefficients
import Sigma.ComplexMeasureSeparation
import Sigma.PairedFunctionalCharge
import ThesisCommon.Analysis.SigmaComplexChargeSeries

/-! Complex product-dual functionals have actual unit-variation charges on all
subsets, agreeing with evaluation on both generated Boolean algebras. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace
attribute [local instance] complexPairedJLGroup complexPairedJLSpace complexPairedJLDualGroup

def complexPairedFunctionalCharge {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (Uinf : Ultrafilter Point)
    (φ : (ComplexJL B × ComplexJL Bt) →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) : ComplexPairedMeasure :=
  complexLpChargeSeries (complexPairedJLCoefficients hB hBt hInf htInf e et φ)
    (by simpa using hφ) (fun p => (pairedAtomCharge hB hBt e et Uinf p).toComplex)

theorem complexPairedFunctionalCharge_eq_of_lifts {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (Uinf : Ultrafilter Point)
    (φ : (ComplexJL B × ComplexJL Bt) →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1)
    (A D : Set Point) (f : C(AUCompactum B,ℝ)) (g : C(AUCompactum Bt,ℝ))
    (hf : ∀ p, atomCharge hB Uinf p A = f p) (hg : ∀ p, atomCharge hBt Uinf p D = g p) :
    complexPairedFunctionalCharge hB hBt hInf htInf e et Uinf φ hφ (pairedBaseSet A D) =
      φ (⟨complexRestrictToBase B (complexLiftRealContinuous f),complexRestrictToBase_mem hB _⟩,
         ⟨complexRestrictToBase Bt (complexLiftRealContinuous g),complexRestrictToBase_mem hBt _⟩) := by
  let fJL : ComplexJL B := ⟨complexRestrictToBase B (complexLiftRealContinuous f),
    complexRestrictToBase_mem hB _⟩
  let gJL : ComplexJL Bt := ⟨complexRestrictToBase Bt (complexLiftRealContinuous g),
    complexRestrictToBase_mem hBt _⟩
  have hs := complexPairedJLCoefficients_apply_hasSum hB hBt hInf htInf e et φ fJL gJL
  change (∑' p, complexPairedJLCoefficients hB hBt hInf htInf e et φ p *
    (pairedAtomCharge hB hBt e et Uinf p (pairedBaseSet A D) : ℂ)) = _
  rw [← hs.tsum_eq]
  apply tsum_congr
  rintro ⟨side,p⟩
  congr 1
  cases side
  · change (putInCopy false (atomCharge hB Uinf (compactumAtomEquiv e p)) (pairedBaseSet A D) : ℂ) = _
    rw [putInCopy_false_pairedBaseSet,hf]
    exact (congrArg (fun u : C(AUCompactum B,ℂ) => u (compactumAtomEquiv e p))
      (complexJLContinuousEquiv_restrict hB hInf (complexLiftRealContinuous f)
        (complexRestrictToBase_mem hB _))).symm
  · change (putInCopy true (atomCharge hBt Uinf (compactumAtomEquiv et p)) (pairedBaseSet A D) : ℂ) = _
    rw [putInCopy_true_pairedBaseSet,hg]
    exact (congrArg (fun u : C(AUCompactum Bt,ℂ) => u (compactumAtomEquiv et p))
      (complexJLContinuousEquiv_restrict hBt htInf (complexLiftRealContinuous g)
        (complexRestrictToBase_mem hBt _))).symm

theorem complexPairedFunctionalCharge_generated {Λ : Type} {B Bt : Set (Set Point)}
    (hB : AlmostDisjoint B) (hBt : AlmostDisjoint Bt) (hInf : B.Infinite) (htInf : Bt.Infinite)
    (e : Λ ≃ B) (et : Λ ≃ Bt) (Uinf : Ultrafilter Point)
    (hfree : (Uinf : Filter Point) ≤ Filter.cofinite)
    (havoid : ∀ b ∈ B, b ∉ Uinf) (havoidt : ∀ b ∈ Bt, b ∉ Uinf)
    (φ : (ComplexJL B × ComplexJL Bt) →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1)
    {A D : Set Point} (hA : A ∈ generatedAlgebra B) (hD : D ∈ generatedAlgebra Bt) :
    ∃ (hmemA : complexCharacteristic A ∈ ComplexJL B)
      (hmemD : complexCharacteristic D ∈ ComplexJL Bt),
      complexPairedFunctionalCharge hB hBt hInf htInf e et Uinf φ hφ (pairedBaseSet A D) =
        φ (⟨complexCharacteristic A,hmemA⟩,⟨complexCharacteristic D,hmemD⟩) := by
  obtain ⟨f,hf⟩ := atomLiftable_generated hB Uinf hfree havoid hA
  obtain ⟨g,hg⟩ := atomLiftable_generated hBt Uinf hfree havoidt hD
  have hrf : complexRestrictToBase B (complexLiftRealContinuous f) = complexCharacteristic A := by
    rw [complexRestrict_lift_real,atomLift_restrict hB Uinf hf,complexAmbientOfReal_characteristic]
  have hrg : complexRestrictToBase Bt (complexLiftRealContinuous g) = complexCharacteristic D := by
    rw [complexRestrict_lift_real,atomLift_restrict hBt Uinf hg,complexAmbientOfReal_characteristic]
  refine ⟨hrf ▸ complexRestrictToBase_mem hB _,hrg ▸ complexRestrictToBase_mem hBt _,?_⟩
  simpa only [hrf,hrg] using complexPairedFunctionalCharge_eq_of_lifts
    hB hBt hInf htInf e et Uinf φ hφ A D f g hf hg

end SigmaNonprimarity

