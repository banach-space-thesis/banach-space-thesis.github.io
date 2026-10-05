import Sigma.ComplexNormingEmbedding
import Sigma.ComplexNormingTransport

/-! The complex modulus-coordinate criterion: failure of the desired property
is equivalent to an isomorphic closed complex vector subspace of ℓ∞ that is
closed under coordinatewise complex modulus. -/
noncomputable section
open scoped BoundedContinuousFunction
namespace SigmaNonprimarity

def complexPointwiseModulus (f : ℕ →ᵇ ℂ) : ℕ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => (‖f n‖ : ℂ)) ‖f‖ (fun n => by simpa using f.norm_coe_le_norm n)

@[simp] theorem complexPointwiseModulus_apply (f : ℕ →ᵇ ℂ) (n : ℕ) :
    complexPointwiseModulus f n = (‖f n‖ : ℂ) := rfl

def IsomorphicToComplexSublatticeEllInfinity (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] : Prop :=
  ∃ S : Submodule ℂ (ℕ →ᵇ ℂ), IsClosed (S : Set (ℕ →ᵇ ℂ)) ∧
    (∀ f ∈ S, complexPointwiseModulus f ∈ S) ∧ Nonempty (E ≃L[ℂ] S)

def complexSubmoduleEvaluation {I : Type*} [TopologicalSpace I]
    (S : Submodule ℂ (I →ᵇ ℂ)) (p : I) : S →L[ℂ] ℂ :=
  ({ toFun := fun f => f.val p
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : S →ₗ[ℂ] ℂ).mkContinuous
    1 (by intro f; simpa using f.val.norm_coe_le_norm p)

theorem complexSubmoduleEvaluation_oneNorming {I : Type*} [TopologicalSpace I]
    (S : Submodule ℂ (I →ᵇ ℂ)) (p : ℕ → I) (hp : Function.Surjective p) :
    IsComplexCNorming (E := S) (fun n => complexSubmoduleEvaluation S (p n)) 1 := by
  let e : ℕ → S →L[ℂ] ℂ := fun n => complexSubmoduleEvaluation S (p n)
  have he (n) : ‖e n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    simpa using f.val.norm_coe_le_norm (p n)
  refine ⟨zero_lt_one,le_rfl,he,?_⟩
  intro f
  rw [one_mul]
  have hb := complex_evaluations_bddAbove e he f
  have hn : 0 ≤ ⨆ n, ‖e n f‖ := (norm_nonneg _).trans (le_ciSup hb 0)
  apply (BoundedContinuousFunction.norm_le hn).mpr
  intro q
  obtain ⟨n,rfl⟩ := hp q
  exact le_ciSup hb n

theorem complex_sublattice_of_not_desiredProperty (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (h : ¬ ComplexDesiredProperty E) :
    IsomorphicToComplexSublatticeEllInfinity E := by
  obtain ⟨e,⟨c,he⟩,hmod⟩ := (not_complexDesiredProperty_iff (E := E)).mp h
  let T := complexNormingCoordinates e he.2.2.1
  let S := LinearMap.range T
  have hclosed : IsClosed (S : Set (ℕ →ᵇ ℂ)) :=
    (complexNormingCoordinates_antilipschitz he).isClosed_range T.uniformContinuous
  refine ⟨S,hclosed,?_,⟨complexNormingCoordinatesEquiv he⟩⟩
  rintro f ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := hmod x
  exact ⟨y,BoundedContinuousFunction.ext hy⟩

theorem complex_not_desiredProperty_of_sublattice (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (h : IsomorphicToComplexSublatticeEllInfinity E) :
    ¬ ComplexDesiredProperty E := by
  obtain ⟨S,_,hmod,⟨T⟩⟩ := h
  apply not_complexDesiredProperty_of_equiv (E := E) (F := S) T
  apply (not_complexDesiredProperty_iff (E := S)).mpr
  refine ⟨fun n => complexSubmoduleEvaluation S n,
    ⟨1,complexSubmoduleEvaluation_oneNorming S id Function.surjective_id⟩,?_⟩
  intro f
  exact ⟨⟨complexPointwiseModulus f.val,hmod f.val f.property⟩,fun _ => rfl⟩

theorem complex_sublattice_iff_not_desiredProperty (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] :
    IsomorphicToComplexSublatticeEllInfinity E ↔ ¬ ComplexDesiredProperty E :=
  ⟨complex_not_desiredProperty_of_sublattice E,complex_sublattice_of_not_desiredProperty E⟩

end SigmaNonprimarity

