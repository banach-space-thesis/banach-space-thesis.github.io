import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.UniformSpace.CompleteSeparated
import BanachIsometric.ProjectiveComparison
import BanachIsometric.CofinalQuotientDimension

/-!
# Normed quotients and the projective system of an increasing seminorm grading

Each quotient norm is constructed from the specified seminorm, rather than
postulated. The separation quotient of a tagged seminormed copy gives a normed
model of the algebraic quotient by its kernel. For `p ≤ q`, the canonical factor
map is a surjective contraction and preserves the original complex action.
-/

noncomputable section

namespace BanachIsometric

open UniformSpace
open scoped Topology Uniformity

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- A type tag allowing the norm and uniformity of one seminorm to coexist
with an independent locally convex topology on the original module. -/
def SeminormModel (_p : Seminorm ℂ X) : Type _ := X

instance (p : Seminorm ℂ X) : AddCommGroup (SeminormModel p) :=
  inferInstanceAs (AddCommGroup X)

instance (p : Seminorm ℂ X) : Module ℂ (SeminormModel p) :=
  inferInstanceAs (Module ℂ X)

instance (p : Seminorm ℂ X) : SeminormedAddCommGroup (SeminormModel p) :=
  p.toAddGroupSeminorm.toSeminormedAddCommGroup

instance (p : Seminorm ℂ X) : NormedSpace ℂ (SeminormModel p) where
  norm_smul_le a x := (map_smul_eq_mul p a x).le

@[simp] theorem norm_seminormModel (p : Seminorm ℂ X) (x : SeminormModel p) :
    ‖x‖ = p x := rfl

/-- The identity algebraic equivalence retains the original scalar action. -/
def toSeminormModel (p : Seminorm ℂ X) : X ≃ₗ[ℂ] SeminormModel p :=
  LinearEquiv.refl ℂ X

/-- A normed model of the quotient by the zero-kernel of the given seminorm. -/
abbrev SeminormQuotient (p : Seminorm ℂ X) := SeparationQuotient (SeminormModel p)

/-- The canonical projection, initially as an algebraic linear map so that no
ambient topology or continuity of `p` is silently assumed. -/
def seminormQuotientMap (p : Seminorm ℂ X) : X →ₗ[ℂ] SeminormQuotient p :=
  (SeparationQuotient.mkCLM ℂ (SeminormModel p)).toLinearMap.comp
    (toSeminormModel p).toLinearMap

@[simp] theorem seminormQuotientMap_norm (p : Seminorm ℂ X) (x : X) :
    ‖seminormQuotientMap p x‖ = p x := rfl

theorem seminormQuotientMap_surjective (p : Seminorm ℂ X) :
    Function.Surjective (seminormQuotientMap p) := by
  change Function.Surjective (SeparationQuotient.mk : SeminormModel p → SeminormQuotient p)
  exact SeparationQuotient.surjective_mk

/-- The actual scalar submodule on which the seminorm vanishes. -/
def seminormKernel (p : Seminorm ℂ X) : Submodule ℂ X := LinearMap.ker (seminormQuotientMap p)

@[simp] theorem mem_seminormKernel (p : Seminorm ℂ X) (x : X) :
    x ∈ seminormKernel p ↔ p x = 0 := by
  change seminormQuotientMap p x = 0 ↔ p x = 0
  rw [← norm_eq_zero, seminormQuotientMap_norm]

/-- The normed separation model is algebraically exactly the requested quotient
`X / ker p`. Its constructed norm assigns `p x` to the class of `x`. -/
def seminormQuotientEquiv (p : Seminorm ℂ X) :
    (X ⧸ seminormKernel p) ≃ₗ[ℂ] SeminormQuotient p :=
  (seminormQuotientMap p).quotKerEquivOfSurjective (seminormQuotientMap_surjective p)

@[simp] theorem seminormQuotientEquiv_mk (p : Seminorm ℂ X) (x : X) :
    seminormQuotientEquiv p (Submodule.Quotient.mk x) = seminormQuotientMap p x := rfl

@[simp] theorem seminormQuotientEquiv_mk_norm (p : Seminorm ℂ X) (x : X) :
    ‖seminormQuotientEquiv p (Submodule.Quotient.mk x)‖ = p x := rfl

private def seminormFactorOnModel {p q : Seminorm ℂ X} (hpq : p ≤ q) :
    SeminormModel q →L[ℂ] SeminormQuotient p :=
  LinearMap.mkContinuous
    { toFun := fun x => seminormQuotientMap p x
      map_add' := fun x y => (seminormQuotientMap p).map_add x y
      map_smul' := fun a x => (seminormQuotientMap p).map_smul a x }
    1 (by intro x; simpa only [seminormQuotientMap_norm, norm_seminormModel, one_mul]
      using hpq x)

/-- The canonical normed-quotient factor associated to `p ≤ q`. -/
def seminormFactor {p q : Seminorm ℂ X} (hpq : p ≤ q) :
    SeminormQuotient q →L[ℂ] SeminormQuotient p :=
  SeparationQuotient.liftCLM (seminormFactorOnModel hpq)
    (fun _ _ h => (h.map (seminormFactorOnModel hpq).continuous).eq)

@[simp] theorem seminormFactor_quotientMap {p q : Seminorm ℂ X} (hpq : p ≤ q) (x : X) :
    seminormFactor hpq (seminormQuotientMap q x) = seminormQuotientMap p x := rfl

theorem seminormFactor_norm_le {p q : Seminorm ℂ X} (hpq : p ≤ q)
    (x : SeminormQuotient q) : ‖seminormFactor hpq x‖ ≤ ‖x‖ := by
  obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective q x
  simpa only [seminormFactor_quotientMap, seminormQuotientMap_norm] using hpq x

theorem seminormFactor_opNorm_le {p q : Seminorm ℂ X} (hpq : p ≤ q) :
    ‖seminormFactor hpq‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using seminormFactor_norm_le hpq x

theorem seminormFactor_surjective {p q : Seminorm ℂ X} (hpq : p ≤ q) :
    Function.Surjective (seminormFactor hpq) := by
  intro y
  obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective p y
  exact ⟨seminormQuotientMap q x, rfl⟩

@[simp] theorem seminormFactor_refl (p : Seminorm ℂ X) :
    seminormFactor (le_refl p) = ContinuousLinearMap.id ℂ (SeminormQuotient p) := by
  ext y
  obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective p y
  rfl

theorem seminormFactor_comp {p q r : Seminorm ℂ X} (hpq : p ≤ q) (hqr : q ≤ r) :
    (seminormFactor hpq).comp (seminormFactor hqr) = seminormFactor (hpq.trans hqr) := by
  ext y
  obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective r y
  rfl

/-- The Banach completion of the normed quotient attached to a seminorm. -/
abbrev SeminormCompletion (p : Seminorm ℂ X) := Completion (SeminormQuotient p)

/-- The canonical map from the original algebraic module to the completion of
its seminorm quotient. Continuity in the original topology is established below
from the defining-seminorm hypothesis. -/
def seminormCompletionMap (p : Seminorm ℂ X) : X →ₗ[ℂ] SeminormCompletion p :=
  (Completion.toComplL : SeminormQuotient p →L[ℂ] SeminormCompletion p).toLinearMap.comp
    (seminormQuotientMap p)

@[simp] theorem seminormCompletionMap_norm (p : Seminorm ℂ X) (x : X) :
    ‖seminormCompletionMap p x‖ = p x := by
  change ‖((seminormQuotientMap p x : SeminormQuotient p) : SeminormCompletion p)‖ = p x
  rw [Completion.norm_coe, seminormQuotientMap_norm]

theorem seminormCompletionMap_denseRange (p : Seminorm ℂ X) :
    DenseRange (seminormCompletionMap p) := by
  apply (Completion.denseRange_coe :
    DenseRange ((↑) : SeminormQuotient p → SeminormCompletion p)).mono
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := seminormQuotientMap_surjective p y
  exact ⟨x, rfl⟩

/-- A canonical bonding contraction between completed normed quotients. It is
the unique continuous extension of the factor between the dense quotients. -/
def completedSeminormFactor {p q : Seminorm ℂ X} (hpq : p ≤ q) :
    SeminormCompletion q →L[ℂ] SeminormCompletion p :=
  ((Completion.toComplL : SeminormQuotient p →L[ℂ] SeminormCompletion p).comp
    (seminormFactor hpq)).extend
    (Completion.toComplL : SeminormQuotient q →L[ℂ] SeminormCompletion q)
    Completion.denseRange_coe (Completion.isUniformInducing_coe _)

@[simp] theorem completedSeminormFactor_coe {p q : Seminorm ℂ X} (hpq : p ≤ q)
    (x : SeminormQuotient q) :
    completedSeminormFactor hpq (x : SeminormCompletion q) =
      ((seminormFactor hpq x : SeminormQuotient p) : SeminormCompletion p) := by
  exact ContinuousLinearMap.extend_eq _ _ _ _ x

@[simp] theorem completedSeminormFactor_completionMap {p q : Seminorm ℂ X}
    (hpq : p ≤ q) (x : X) :
    completedSeminormFactor hpq (seminormCompletionMap q x) = seminormCompletionMap p x := by
  change completedSeminormFactor hpq
    ((seminormQuotientMap q x : SeminormQuotient q) : SeminormCompletion q) = _
  rw [completedSeminormFactor_coe, seminormFactor_quotientMap]
  rfl

theorem completedSeminormFactor_norm_le {p q : Seminorm ℂ X} (hpq : p ≤ q)
    (x : SeminormCompletion q) : ‖completedSeminormFactor hpq x‖ ≤ ‖x‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_le (completedSeminormFactor hpq).continuous.norm continuous_norm
  · intro y
    simpa only [completedSeminormFactor_coe, Completion.norm_coe] using
      seminormFactor_norm_le hpq y

theorem completedSeminormFactor_opNorm_le {p q : Seminorm ℂ X} (hpq : p ≤ q) :
    ‖completedSeminormFactor hpq‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using completedSeminormFactor_norm_le hpq x

/-- Completed factors have dense range; surjectivity of the uncompleted factor
puts the entire dense target quotient inside their range. -/
theorem completedSeminormFactor_denseRange {p q : Seminorm ℂ X} (hpq : p ≤ q) :
    DenseRange (completedSeminormFactor hpq) := by
  apply (Completion.denseRange_coe :
    DenseRange ((↑) : SeminormQuotient p → SeminormCompletion p)).mono
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := seminormFactor_surjective hpq y
  refine ⟨(x : SeminormCompletion q), ?_⟩
  rw [completedSeminormFactor_coe, hx]

@[simp] theorem completedSeminormFactor_refl (p : Seminorm ℂ X) :
    completedSeminormFactor (le_refl p) = ContinuousLinearMap.id ℂ (SeminormCompletion p) := by
  apply ContinuousLinearMap.coeFn_injective
  apply Completion.ext (completedSeminormFactor (le_refl p)).continuous continuous_id
  intro y
  simp only [completedSeminormFactor_coe, seminormFactor_refl, ContinuousLinearMap.id_apply]
  rfl

theorem completedSeminormFactor_comp {p q r : Seminorm ℂ X}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    (completedSeminormFactor hpq).comp (completedSeminormFactor hqr) =
      completedSeminormFactor (hpq.trans hqr) := by
  apply ContinuousLinearMap.coeFn_injective
  apply Completion.ext
    ((completedSeminormFactor hpq).continuous.comp (completedSeminormFactor hqr).continuous)
    (completedSeminormFactor (hpq.trans hqr)).continuous
  intro y
  change completedSeminormFactor hpq (completedSeminormFactor hqr y) = _
  simp only [completedSeminormFactor_coe]
  exact congrArg ((↑) : SeminormQuotient p → SeminormCompletion p)
    (DFunLike.congr_fun (seminormFactor_comp hpq hqr) y)

/-- A single completion coordinate induces exactly the original seminorm's
uniformity on its tagged model, even when the seminorm has a nonzero kernel. -/
theorem seminormCompletionMap_isUniformInducing_model (p : Seminorm ℂ X) :
    IsUniformInducing (fun x : SeminormModel p => seminormCompletionMap p x) := by
  change IsUniformInducing (fun x : SeminormModel p =>
    ((SeparationQuotient.mk x : SeminormQuotient p) : SeminormCompletion p))
  exact (Completion.isUniformInducing_coe _).comp SeparationQuotient.isUniformInducing_mk

section OriginalUniformity

variable [UniformSpace X] [IsUniformAddGroup X]

/-- The canonical product map pulls back the product uniformity to the given
defining-seminorm uniformity. This proves the embedding condition used in the
projective comparison theorem rather than adding it as a hypothesis. -/
theorem seminormCompletionProduct_isUniformInducing
    (p : ℕ → Seminorm ℂ X) (hp : WithSeminorms p) :
    IsUniformInducing (projectiveProductMap (fun i => seminormCompletionMap (p i))) := by
  apply isUniformInducing_iff_uniformSpace.mpr
  have hcoord (i : ℕ) :
      UniformSpace.comap (seminormCompletionMap (p i))
        (inferInstance : UniformSpace (SeminormCompletion (p i))) =
      (p i).toAddGroupSeminorm.toSeminormedAddCommGroup.toUniformSpace := by
    exact (seminormCompletionMap_isUniformInducing_model (p i)).comap_uniformSpace
  calc
    UniformSpace.comap (projectiveProductMap (fun i => seminormCompletionMap (p i)))
        (inferInstance : UniformSpace (∀ i, SeminormCompletion (p i))) =
        ⨅ i, UniformSpace.comap (seminormCompletionMap (p i))
          (inferInstance : UniformSpace (SeminormCompletion (p i))) := by
      simp only [Pi.uniformSpace_eq, UniformSpace.comap_iInf, ← UniformSpace.comap_comap]
      rfl
    _ = ⨅ i, (p i).toAddGroupSeminorm.toSeminormedAddCommGroup.toUniformSpace :=
      iInf_congr hcoord
    _ = (inferInstance : UniformSpace X) :=
      (SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf p).mp hp |>.symm

end OriginalUniformity

/-- The actual completed quotient inverse limit for an increasing grading,
with the topology inherited from the product of Banach completions. -/
def seminormLimitSubmodule (p : ℕ → Seminorm ℂ X) (hmono : Monotone p) :
    Submodule ℂ (∀ i, SeminormCompletion (p i)) :=
  projectiveCompatibleSubmodule (fun _ _ hij => completedSeminormFactor (hmono hij))

section CompleteOriginal

variable [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]

/-- The canonical projective-limit representation in Theorem C, valid before
any Hilbertianity assertion. No norm on the ambient space is assumed or inferred.
The quotients, their completions, the bonding contractions and their dense ranges
have all been constructed from the specified seminorms above. -/
def seminormInverseLimitEquiv (p : ℕ → Seminorm ℂ X) (hmono : Monotone p)
    (hp : WithSeminorms p) : X ≃L[ℂ] seminormLimitSubmodule p hmono :=
  projectiveComparisonEquivOfComplete
    (fun _ _ hij => completedSeminormFactor (hmono hij))
    (fun i => seminormCompletionMap (p i))
    (fun _ _ hij x => completedSeminormFactor_completionMap (hmono hij) x)
    (fun i => seminormCompletionMap_denseRange (p i))
    (seminormCompletionProduct_isUniformInducing p hp)

/-- The equivalence is canonical: its `i`-th coordinate is the completion of
the class of the original vector, not an arbitrary linear homeomorphism. -/
@[simp] theorem seminormInverseLimitEquiv_apply (p : ℕ → Seminorm ℂ X)
    (hmono : Monotone p) (hp : WithSeminorms p) (x : X) (i : ℕ) :
    (seminormInverseLimitEquiv p hmono hp x).val i = seminormCompletionMap (p i) x := rfl

end CompleteOriginal

/-- Increasing seminorms give an antitone sequence of their actual kernels. -/
theorem seminormKernel_antitone (p : ℕ → Seminorm ℂ X) (hmono : Monotone p) :
    Antitone (fun i => seminormKernel (p i)) := by
  intro i j hij x hx
  rw [mem_seminormKernel] at hx ⊢
  exact le_antisymm ((hmono hij x).trans_eq hx) (apply_nonneg (p i) x)

/-- A defining family on a Hausdorff module separates points algebraically. -/
theorem seminormKernel_iInf_eq_bot [TopologicalSpace X] [T1Space X]
    (p : ℕ → Seminorm ℂ X) (hp : WithSeminorms p) :
    (⨅ i, seminormKernel (p i)) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  by_contra hx0
  obtain ⟨i, hi⟩ := hp.separating_of_T1 x hx0
  exact hi ((mem_seminormKernel (p i) x).mp
    ((Submodule.mem_iInf (fun i => seminormKernel (p i))).mp hx i))

/-- The eventual quotient-dimension threshold for the actual normed quotient
models of a Hausdorff increasing defining grading, including infinite dimension. -/
theorem cofinal_seminorm_quotient_dimension [TopologicalSpace X] [T1Space X]
    (p : ℕ → Seminorm ℂ X) (hmono : Monotone p) (hp : WithSeminorms p)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank ℂ X) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, (n : Cardinal) < Module.rank ℂ (SeminormQuotient (p k)) := by
  obtain ⟨k₀, hk₀⟩ := cofinal_quotient_dimension
    (fun i => seminormKernel (p i)) (seminormKernel_antitone p hmono)
    (seminormKernel_iInf_eq_bot p hp) n hn
  refine ⟨k₀, ?_⟩
  intro k hk
  rw [← (seminormQuotientEquiv (p k)).rank_eq]
  exact hk₀ k hk

end BanachIsometric
