import BanachIsometric.HermitianSpectralInvariants

/-!
# Genuine eigenbasis deletion hyperplanes and their restricted operators

The subspaces are spans of all but one vector of an actual orthonormal basis.
Their dimensions, their orthonormal bases and the traces of the actual
restricted Hermitian forms are proved here.
-/

namespace BanachIsometric

open Set
open scoped BigOperators ComplexConjugate

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def orthonormalDeletionSubmodule (b : OrthonormalBasis ι 𝕜 E) (i : ι) : Submodule 𝕜 E := by
  classical
  exact Submodule.span 𝕜 ((Finset.univ.erase i).image b : Set E)

def orthonormalDeletionBasis (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    OrthonormalBasis (Finset.univ.erase i) 𝕜 (orthonormalDeletionSubmodule b i) := by
  classical
  exact OrthonormalBasis.span b.orthonormal (Finset.univ.erase i)

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem orthonormalDeletionBasis_apply (b : OrthonormalBasis ι 𝕜 E) (i : ι)
    (j : Finset.univ.erase i) :
    (orthonormalDeletionBasis b i j : E) = b j.val := by
  classical
  exact OrthonormalBasis.span_apply b.orthonormal (Finset.univ.erase i) j

omit [FiniteDimensional 𝕜 E] in
theorem orthonormalDeletionSubmodule_finrank (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    Module.finrank 𝕜 (orthonormalDeletionSubmodule b i) = Fintype.card ι - 1 := by
  rw [Module.finrank_eq_card_basis (orthonormalDeletionBasis b i).toBasis,
    Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]

def restrictSesqForm (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (H : Submodule 𝕜 E) :
    H →ₗ⋆[𝕜] H →ₗ[𝕜] 𝕜 := (B.compl₂ H.subtype).comp H.subtype

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem restrictSesqForm_apply (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (H : Submodule 𝕜 E) (x y : H) :
    restrictSesqForm B H x y = B x.val y.val := rfl

omit [FiniteDimensional 𝕜 E] in
theorem restrictSesqForm_hermitian (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜)
    (hB : ∀ x y, star (B x y) = B y x) (H : Submodule 𝕜 E) :
    ∀ x y, star (restrictSesqForm B H x y) = restrictSesqForm B H y x :=
  fun x y => hB x.val y.val

theorem relativeOperator_restrict_eigenvector
    (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (H : Submodule 𝕜 E) (x : H) (a : ℝ)
    (heig : hermitianRelativeOperator B x.val = (a : 𝕜) • x.val) :
    hermitianRelativeOperator (restrictSesqForm B H) x = (a : 𝕜) • x := by
  apply ext_inner_right 𝕜
  intro y
  rw [hermitianRelativeOperator_inner, inner_smul_left]
  change B x.val y.val = star (a : 𝕜) * inner 𝕜 x.val y.val
  rw [← hermitianRelativeOperator_inner, heig, inner_smul_left]
  rfl

theorem re_relativeOperator_eigenvector_diagonal
    (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (hB : ∀ x y, star (B x y) = B y x)
    (x : E) (hx : ‖x‖ = 1) (a : ℝ)
    (heig : hermitianRelativeOperator B x = (a : 𝕜) • x) :
    RCLike.re (B x x) = a := by
  rw [← inner_hermitianRelativeOperator B hB, heig, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hx]
  simp only [RCLike.ofReal_one, one_pow, mul_one, RCLike.ofReal_re]

theorem re_trace_orthonormalDeletion
    (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (hB : ∀ x y, star (B x y) = B y x)
    (b : OrthonormalBasis ι 𝕜 E) (a : ι → ℝ)
    (heig : ∀ j, hermitianRelativeOperator B (b j) = (a j : 𝕜) • b j) (i : ι) :
    RCLike.re (LinearMap.trace 𝕜 (orthonormalDeletionSubmodule b i)
      (hermitianRelativeOperator (restrictSesqForm B (orthonormalDeletionSubmodule b i)))) =
      ∑ j ∈ Finset.univ.erase i, a j := by
  rw [re_trace_relativeOperator_eq_sum _ (restrictSesqForm_hermitian B hB _)
    (orthonormalDeletionBasis b i)]
  simp only [restrictSesqForm_apply, orthonormalDeletionBasis_apply]
  simp_rw [re_relativeOperator_eigenvector_diagonal B hB _ (b.orthonormal.1 _) _ (heig _)]
  exact Finset.sum_coe_sort _ _

end

end BanachIsometric
