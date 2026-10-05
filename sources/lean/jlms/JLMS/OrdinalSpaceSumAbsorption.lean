import JLMS.CZeroSumEquiv
import JLMS.CZeroSumFinite
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-!
# Absorbing the base summand in Kislyakov's block decomposition

An infinite constant c₀ sum absorbs one of its coordinates. Consequently,
if E absorbs F, then the c₀ sum of copies of E also absorbs F. This is the
algebraic step in Kislyakov Corollary 3.1 after the actual block decomposition.
-/

noncomputable section
namespace JLMS
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜]

def cZeroSumSingletonIsometry (E : Type v) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    CZeroSum 𝕜 (fun _ : PUnit.{u + 1} => E) ≃ₗᵢ[𝕜] E :=
  (LinearIsometryEquiv.ofSurjective
    (CZeroSum.singleIsometry (𝕜 := 𝕜) (E := fun _ : PUnit.{u + 1} => E) PUnit.unit)
    (by
      intro x
      refine ⟨x PUnit.unit, ?_⟩
      ext i
      cases i
      simp)).symm

def linearIsometryEquivProdCongr {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (e : E ≃ₗᵢ[𝕜] F) (f : G ≃ₗᵢ[𝕜] H) : E × G ≃ₗᵢ[𝕜] F × H where
  toLinearEquiv := e.toLinearEquiv.prodCongr f.toLinearEquiv
  norm_map' x := by change max ‖e x.1‖ ‖f x.2‖ = _; rw [e.norm_map, f.norm_map]; rfl

/-- Split off one coordinate from an infinite constant c₀ sum. -/
def cZeroSumInfiniteHeadIsometry (I : Type u) [Infinite I] (E : Type v)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    CZeroSum 𝕜 (fun _ : I => E) ≃ₗᵢ[𝕜] E × CZeroSum 𝕜 (fun _ : I => E) := by
  have hcard : Cardinal.mk (PUnit.{u + 1} ⊕ I) = Cardinal.mk I := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_punit]
    exact Cardinal.add_eq_right (Cardinal.aleph0_le_mk I)
      (Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_mk I))
  let e : PUnit.{u + 1} ⊕ I ≃ I := Classical.choice (Cardinal.eq.mp hcard)
  exact (CZeroSum.reindex (𝕜 := 𝕜) (E := fun _ : I => E) e).trans
    (CZeroSum.sumIsometry.trans
      (linearIsometryEquivProdCongr (cZeroSumSingletonIsometry E) (LinearIsometryEquiv.refl 𝕜 _)))

/-- The absorption step: F×E≃E implies F×c₀(I,E)≃c₀(I,E) for infinite I. -/
def cZeroSumAbsorbs (I : Type u) [Infinite I] {E F : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : (F × E) ≃L[𝕜] E) :
    (F × CZeroSum 𝕜 (fun _ : I => E)) ≃L[𝕜] CZeroSum 𝕜 (fun _ : I => E) :=
  let h := (cZeroSumInfiniteHeadIsometry (𝕜 := 𝕜) I E).toContinuousLinearEquiv
  ((ContinuousLinearEquiv.refl 𝕜 F).prodCongr h).trans
    ((ContinuousLinearEquiv.prodAssoc 𝕜 F E _).symm.trans
      ((e.prodCongr (ContinuousLinearEquiv.refl 𝕜 _)).trans h.symm))

end JLMS
