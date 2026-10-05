import JLMS.CZeroSum
import Mathlib.LinearAlgebra.Pi
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Reindexing and splitting Banach c₀ sums

These are the direct-sum identities used in Kislyakov's classification.
All maps act on the concrete dependent c₀ sums and preserve the supremum norm.
-/

noncomputable section
open Filter Topology
namespace JLMS
namespace CZeroSum
universe u u' v w
variable {𝕜 : Type w} [RCLike 𝕜] {I : Type u} {J : Type u'}
  {E : I → Type v} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- Restriction along an injection preserves vanishing at infinity. -/
def comap (e : J → I) (he : Function.Injective e) (x : CZeroSum 𝕜 E) :
    CZeroSum 𝕜 (fun j => E (e j)) :=
  CZeroSum.mk (fun j => x (e j)) (x.tendsto_norm.comp he.tendsto_cofinite)

@[simp] theorem comap_apply (e : J → I) (he : Function.Injective e)
    (x : CZeroSum 𝕜 E) (j : J) : comap e he x j = x (e j) := rfl

theorem norm_comap_le (e : J → I) (he : Function.Injective e) (x : CZeroSum 𝕜 E) :
    ‖comap e he x‖ ≤ ‖x‖ := norm_le (norm_nonneg x) (fun j => x.norm_apply_le_norm (e j))

def comapCLM (e : J → I) (he : Function.Injective e) :
    CZeroSum 𝕜 E →L[𝕜] CZeroSum 𝕜 (fun j => E (e j)) :=
  ({toFun := comap e he
    map_add' x y := by ext j; rfl
    map_smul' c x := by ext j; rfl} :
      CZeroSum 𝕜 E →ₗ[𝕜] CZeroSum 𝕜 (fun j => E (e j))).mkContinuous 1
    (fun x => by simpa only [one_mul] using norm_comap_le e he x)

/-- An equivalence of index sets gives a linear isometric equivalence of
the dependent c₀ sums. -/
def reindex (e : J ≃ I) : CZeroSum 𝕜 E ≃ₗᵢ[𝕜] CZeroSum 𝕜 (fun j => E (e j)) := by
  let L : CZeroSum 𝕜 E →ₗᵢ[𝕜] CZeroSum 𝕜 (fun j => E (e j)) := {
    toFun := comap e e.injective
    map_add' x y := by ext j; rfl
    map_smul' c x := by ext j; rfl
    norm_map' x := by
      apply le_antisymm (norm_comap_le e e.injective x)
      apply norm_le (norm_nonneg _)
      intro i
      obtain ⟨j, rfl⟩ := e.surjective i
      exact (comap e e.injective x).norm_apply_le_norm j
  }
  apply LinearIsometryEquiv.ofSurjective L
  intro y
  let z : ∀ i, E i := Equiv.piCongrLeft E e y
  have hz (j : J) : z (e j) = y j := Equiv.piCongrLeft_apply_apply E e y j
  have hznorm : (fun i => ‖z i‖) = (fun j => ‖y j‖) ∘ e.symm := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp only [hz, Function.comp_apply]
    exact (congrArg (fun j => ‖y j‖) (e.symm_apply_apply j)).symm
  have ht : Tendsto (fun i => ‖z i‖) cofinite (𝓝 0) := by
    rw [hznorm]
    exact y.tendsto_norm.comp e.symm.injective.tendsto_cofinite
  refine ⟨CZeroSum.mk z ht, ?_⟩
  ext j
  exact hz j

@[simp] theorem reindex_apply (e : J ≃ I) (x : CZeroSum 𝕜 E) (j : J) :
    reindex (𝕜 := 𝕜) (E := E) e x j = x (e j) := rfl

section Sum

variable {F : I ⊕ J → Type v} [∀ s, NormedAddCommGroup (F s)]
  [∀ s, NormedSpace 𝕜 (F s)]

def join (x : CZeroSum 𝕜 (fun i => F (.inl i)))
    (y : CZeroSum 𝕜 (fun j => F (.inr j))) : CZeroSum 𝕜 F := by
  let z : ∀ s, F s := fun s => match s with | .inl i => x i | .inr j => y j
  apply CZeroSum.mk z
  apply (tendsto_norm_cofinite_iff_finite z).mpr
  intro ε hε
  apply (((x.finite_norm_ge hε).image Sum.inl).union
    ((y.finite_norm_ge hε).image Sum.inr)).subset
  intro s hs
  cases s with
  | inl i => exact Or.inl ⟨i, hs, rfl⟩
  | inr j => exact Or.inr ⟨j, hs, rfl⟩

@[simp] theorem join_inl (x : CZeroSum 𝕜 (fun i => F (.inl i)))
    (y : CZeroSum 𝕜 (fun j => F (.inr j))) (i : I) : join x y (.inl i) = x i := rfl
@[simp] theorem join_inr (x : CZeroSum 𝕜 (fun i => F (.inl i)))
    (y : CZeroSum 𝕜 (fun j => F (.inr j))) (j : J) : join x y (.inr j) = y j := rfl

/-- A sum of two index sets becomes the sup-norm product of the two sums. -/
def sumIsometry : CZeroSum 𝕜 F ≃ₗᵢ[𝕜]
    CZeroSum 𝕜 (fun i => F (.inl i)) × CZeroSum 𝕜 (fun j => F (.inr j)) where
  toFun x := (comap Sum.inl Sum.inl_injective x, comap Sum.inr Sum.inr_injective x)
  invFun p := join p.1 p.2
  left_inv x := by ext s; cases s <;> rfl
  right_inv p := by apply Prod.ext <;> ext i <;> rfl
  map_add' x y := by apply Prod.ext <;> ext i <;> rfl
  map_smul' c x := by apply Prod.ext <;> ext i <;> rfl
  norm_map' x := by
    rw [Prod.norm_def]
    apply le_antisymm (max_le (norm_comap_le _ _ _) (norm_comap_le _ _ _))
    apply norm_le (le_trans (norm_nonneg _) (le_max_left _ _))
    intro s
    cases s with
    | inl i => exact ((comap Sum.inl Sum.inl_injective x).norm_apply_le_norm i).trans (le_max_left _ _)
    | inr j => exact ((comap Sum.inr Sum.inr_injective x).norm_apply_le_norm j).trans (le_max_right _ _)

end Sum

/-- An infinite constant c₀ sum is isometric to its square. -/
def infiniteSquareIsometry (I : Type u) [Infinite I] (X : Type v)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    CZeroSum 𝕜 (fun _ : I => X) ≃ₗᵢ[𝕜]
      CZeroSum 𝕜 (fun _ : I => X) × CZeroSum 𝕜 (fun _ : I => X) := by
  have hcard : Cardinal.mk (I ⊕ I) = Cardinal.mk I := by
    simpa only [Cardinal.mk_sum, Cardinal.lift_id] using
      Cardinal.add_eq_self (Cardinal.aleph0_le_mk I)
  let e : I ⊕ I ≃ I := Classical.choice (Cardinal.eq.mp hcard)
  exact (reindex (𝕜 := 𝕜) (E := fun _ : I => X) e).trans sumIsometry

end CZeroSum
end JLMS
