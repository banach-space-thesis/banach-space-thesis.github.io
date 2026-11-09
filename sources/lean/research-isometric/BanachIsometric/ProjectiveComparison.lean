import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Complete spaces and inverse limits of dense quotient models

The comparison proof uses finite-coordinate neighborhoods, not a chosen Cauchy
sequence. Every compatible tuple is in the closure of the comparison image:
approximate its largest requested coordinate and use the bonding maps. A
uniform embedding from a complete space has closed image, hence is onto.
-/

noncomputable section

namespace BanachIsometric

open Set
open scoped Topology

variable {X : Type*} [AddCommGroup X] [Module ℂ X]
variable {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]

/-- Compatible tuples for all the canonical maps from later indices to earlier
ones. This uses the subspace topology inherited from the full product. -/
def projectiveCompatibleSubmodule
    (bond : ∀ i j : ℕ, i ≤ j → E j →L[ℂ] E i) : Submodule ℂ (∀ i, E i) where
  carrier := {y | ∀ i j (hij : i ≤ j), bond i j hij (y j) = y i}
  zero_mem' := by intro i j hij; simp
  add_mem' := by
    intro x y hx hy i j hij
    simp only [Pi.add_apply, map_add, hx i j hij, hy i j hij]
  smul_mem' := by
    intro a x hx i j hij
    simp only [Pi.smul_apply, map_smul, hx i j hij]

def projectiveProductMap (q : ∀ i, X →ₗ[ℂ] E i) : X →ₗ[ℂ] ∀ i, E i := LinearMap.pi q

@[simp] theorem projectiveProductMap_apply (q : ∀ i, X →ₗ[ℂ] E i) (x : X) (i : ℕ) :
    projectiveProductMap q x i = q i x := rfl

def projectiveComparison
    (bond : ∀ i j : ℕ, i ≤ j → E j →L[ℂ] E i) (q : ∀ i, X →ₗ[ℂ] E i)
    (hcomm : ∀ i j (hij : i ≤ j) x, bond i j hij (q j x) = q i x) :
    X →ₗ[ℂ] projectiveCompatibleSubmodule bond where
  toFun x := ⟨projectiveProductMap q x, fun i j hij => hcomm i j hij x⟩
  map_add' x y := Subtype.ext <| (projectiveProductMap q).map_add x y
  map_smul' a x := Subtype.ext <| (projectiveProductMap q).map_smul a x

/-- Every compatible tuple lies in the closure of the image of the original
space whenever each coordinate projection has dense range. -/
theorem projectiveCompatible_mem_closure_range
    (bond : ∀ i j : ℕ, i ≤ j → E j →L[ℂ] E i) (q : ∀ i, X →ₗ[ℂ] E i)
    (hcomm : ∀ i j (hij : i ≤ j) x, bond i j hij (q j x) = q i x)
    (hdense : ∀ i, DenseRange (q i)) (y : projectiveCompatibleSubmodule bond) :
    y.val ∈ closure (Set.range (projectiveProductMap q)) := by
  classical
  apply mem_closure_iff.mpr
  intro U hU hyU
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU y.val hyU
  let k : ℕ := I.sup id
  have hik (i : ℕ) (hi : i ∈ I) : i ≤ k := by
    exact Finset.le_sup (f := id) hi
  let W : Set (E k) := ⋂ i : I, (bond i.val k (hik i.val i.property)) ⁻¹' u i.val
  have hW : IsOpen W := by
    apply isOpen_iInter_of_finite
    intro i
    exact (hu i.val i.property).1.preimage (bond i.val k (hik i.val i.property)).continuous
  have hyW : y.val k ∈ W := by
    apply Set.mem_iInter.mpr
    intro i
    change bond i.val k (hik i.val i.property) (y.val k) ∈ u i.val
    rw [y.property i.val k (hik i.val i.property)]
    exact (hu i.val i.property).2
  obtain ⟨x, hx⟩ := (hdense k).exists_mem_open hW ⟨_, hyW⟩
  refine ⟨projectiveProductMap q x, hsub ?_, ⟨x, rfl⟩⟩
  intro i hi
  have hxi := Set.mem_iInter.mp hx (⟨i, hi⟩ : I)
  change bond i k (hik i hi) (q k x) ∈ u i at hxi
  rwa [hcomm i k (hik i hi) x] at hxi

/-- A complete original space is topologically and linearly the compatible
tuple space if the canonical product map is uniform inducing and each quotient
coordinate is dense. The uniform-inducing condition fixes the original topology
and is established from the given seminorm family in the concrete application. -/
def projectiveComparisonEquivOfComplete
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]
    (bond : ∀ i j : ℕ, i ≤ j → E j →L[ℂ] E i) (q : ∀ i, X →ₗ[ℂ] E i)
    (hcomm : ∀ i j (hij : i ≤ j) x, bond i j hij (q j x) = q i x)
    (hdense : ∀ i, DenseRange (q i))
    (hUI : IsUniformInducing (projectiveProductMap q)) :
    X ≃L[ℂ] projectiveCompatibleSubmodule bond := by
  let f := projectiveComparison bond q hcomm
  have hfUI : IsUniformInducing f := by
    apply ((isUniformInducing_val
      (projectiveCompatibleSubmodule bond : Set (∀ i, E i))).isUniformInducing_comp_iff).mp
    exact hUI
  have hclosed : IsClosed (Set.range (projectiveProductMap q)) :=
    hUI.isUniformEmbedding.isClosedEmbedding.isClosed_range
  have hsurj : Function.Surjective f := by
    intro y
    have hy := projectiveCompatible_mem_closure_range bond q hcomm hdense y
    rw [hclosed.closure_eq] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let e : X ≃ₗ[ℂ] projectiveCompatibleSubmodule bond :=
    LinearEquiv.ofBijective f ⟨hfUI.injective, hsurj⟩
  have heUI : IsUniformInducing (e : X → projectiveCompatibleSubmodule bond) := hfUI
  refine { e with
    continuous_toFun := heUI.uniformContinuous.continuous
    continuous_invFun := ?_ }
  apply heUI.isInducing.continuous_iff.mpr
  change Continuous (fun y : projectiveCompatibleSubmodule bond => e (e.symm y))
  have hfun : (fun y : projectiveCompatibleSubmodule bond => e (e.symm y)) = id :=
    funext e.apply_symm_apply
  rw [hfun]
  exact continuous_id

@[simp] theorem projectiveComparisonEquivOfComplete_apply
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]
    (bond : ∀ i j : ℕ, i ≤ j → E j →L[ℂ] E i) (q : ∀ i, X →ₗ[ℂ] E i)
    (hcomm : ∀ i j (hij : i ≤ j) x, bond i j hij (q j x) = q i x)
    (hdense : ∀ i, DenseRange (q i))
    (hUI : IsUniformInducing (projectiveProductMap q)) (x : X) :
    projectiveComparisonEquivOfComplete bond q hcomm hdense hUI x =
      projectiveComparison bond q hcomm x := rfl

theorem projectiveComparison_equiv_of_complete
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]
    (bond : ∀ i j : ℕ, i ≤ j → E j →L[ℂ] E i) (q : ∀ i, X →ₗ[ℂ] E i)
    (hcomm : ∀ i j (hij : i ≤ j) x, bond i j hij (q j x) = q i x)
    (hdense : ∀ i, DenseRange (q i))
    (hUI : IsUniformInducing (projectiveProductMap q)) :
    Nonempty (X ≃L[ℂ] projectiveCompatibleSubmodule bond) :=
  ⟨projectiveComparisonEquivOfComplete bond q hcomm hdense hUI⟩

end BanachIsometric
