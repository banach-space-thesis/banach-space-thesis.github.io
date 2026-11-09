import BanachIsometric.EilenbergZilberTensorComposite

/-! Fixed homogeneous chains on universal simplex pairs extend by
pushforward to natural linear operators on the tensor complex. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW
open scoped TensorProduct DirectSum

variable {X Y X' Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

abbrev UniversalTensorHomotopies (n : ℕ) :=
  ∀ p q : ℕ, p + q = n → rawTensorTotalDegree (Simplex p) (Simplex q) (n + 1)

def universalTensorHomotopyBidegree {n p q : ℕ} (K : UniversalTensorHomotopies n)
    (h : p + q = n) : RawTensorChains X Y p q →ₗ[ℚ] rawTensorTotalDegree X Y (n + 1) :=
  TensorProduct.lift (Finsupp.linearCombination ℚ (fun σ =>
    Finsupp.linearCombination ℚ (fun τ => rawBigradedTensorMapHomogeneous σ τ (n + 1) (K p q h))))

def universalTensorHomotopyEvaluation {n : ℕ} (K : UniversalTensorHomotopies n) :
    rawTensorTotalDegree X Y n →ₗ[ℚ] rawTensorTotalDegree X Y (n + 1) :=
  (DirectSum.toModule ℚ (ℕ × ℕ) (rawTensorTotalDegree X Y (n + 1))
    (fun ij => if h : ij.1 + ij.2 = n then universalTensorHomotopyBidegree K h else 0)).comp
    (rawTensorTotalDegree X Y n).subtype

theorem universalTensorHomotopyEvaluation_single {n p q : ℕ} (K : UniversalTensorHomotopies n)
    (h : p + q = n) (σ : RawSingularSimplex X p) (τ : RawSingularSimplex Y q) :
    universalTensorHomotopyEvaluation K
      (rawTensorHomogeneousInclusion h (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1)) =
        rawBigradedTensorMapHomogeneous σ τ (n + 1) (K p q h) := by
  simp only [universalTensorHomotopyEvaluation, LinearMap.comp_apply,
    rawTensorHomogeneousInclusion, Submodule.subtype_apply, LinearMap.codRestrict_apply,
    rawTensorInclusion, DirectSum.toModule_lof, dif_pos h, universalTensorHomotopyBidegree,
    TensorProduct.lift.tmul, Finsupp.linearCombination_single, one_smul]

theorem universalTensorHomotopyEvaluation_generator {n p q : ℕ} (K : UniversalTensorHomotopies n)
    (h : p + q = n) : universalTensorHomotopyEvaluation K (universalTensorHomogeneousGenerator h) =
      K p q h := by
  rw [universalTensorHomogeneousGenerator, universalTensorHomotopyEvaluation_single,
    rawBigradedTensorMapHomogeneous_id]

theorem universalTensorHomotopyEvaluation_naturality {n : ℕ} (K : UniversalTensorHomotopies n)
    (f : C(X, X')) (g : C(Y, Y')) (c : rawTensorTotalDegree X Y n) :
    universalTensorHomotopyEvaluation K (rawBigradedTensorMapHomogeneous f g n c) =
      rawBigradedTensorMapHomogeneous f g (n + 1) (universalTensorHomotopyEvaluation K c) := by
  have he :
      (universalTensorHomotopyEvaluation K).comp (rawBigradedTensorMapHomogeneous f g n) =
        (rawBigradedTensorMapHomogeneous f g (n + 1)).comp (universalTensorHomotopyEvaluation K) := by
    apply rawTensorHomogeneous_linearMap_ext
    intro p q hpq σ τ
    simp only [LinearMap.comp_apply, universalTensorHomotopyEvaluation_single]
    have hpush : rawBigradedTensorMapHomogeneous f g n
        (rawTensorHomogeneousInclusion hpq (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1)) =
          rawTensorHomogeneousInclusion hpq
            (Finsupp.single (f.comp σ) 1 ⊗ₜ[ℚ] Finsupp.single (g.comp τ) 1) := by
      apply Subtype.ext
      change rawBigradedTensorMap f g (rawTensorInclusion X Y p q
        (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1)) = _
      simp only [rawBigradedTensorMap_inclusion, TensorProduct.map_tmul, rawChainMap,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
    rw [hpush, universalTensorHomotopyEvaluation_single]
    exact rawBigradedTensorMapHomogeneous_comp σ τ f g (n + 1) (K p q hpq)
  exact LinearMap.congr_fun he c

end BanachIsometric.SingularEZ
