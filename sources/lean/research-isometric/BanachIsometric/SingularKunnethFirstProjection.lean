import BanachIsometric.SingularHomologyPoint
import BanachIsometric.SingularKunnethPairing

/-! Projecting to the first factor is the degree-(n,0) component of
Künneth followed by the degree-zero augmentation of the second factor. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW
open scoped TensorProduct

variable (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]

def awProductFst : C(X × Y, X) := ⟨Prod.fst, continuous_fst⟩

theorem frontSimplex_all (n : ℕ) : frontSimplex n n le_rfl = ContinuousMap.id (Simplex n) := by
  change simplexMap (intervalVertex 0 n n (by omega)) = _
  have h : intervalVertex 0 n n (by omega) = id := by
    funext i
    apply Fin.ext
    exact Nat.zero_add i.val
  rw [h, simplexMap_id]

def rawKunnethFirstProjection (n : ℕ) :
    (RawHomology X n ⊗[ℚ] RawHomology Y 0) →ₗ[ℚ] RawHomology X n :=
  (TensorProduct.rid ℚ (RawHomology X n)).toLinearMap.comp
    (TensorProduct.map LinearMap.id (rawFullZeroAugmentation Y))

theorem rawKunnethFirstProjection_chain (n : ℕ) (c : RawRationalChains (X × Y) n) :
    rawKunnethFirstProjection X Y n (rawKunnethChainComponent X Y n n 0 c) =
      rawFactorHomologyProjection X n (rawChainMap (awProductFst X Y) n c) := by
  have h : (rawKunnethFirstProjection X Y n).comp (rawKunnethChainComponent X Y n n 0) =
      (rawFactorHomologyProjection X n).comp (rawChainMap (awProductFst X Y) n) := by
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext_ring
    have hfront : simplexFrontProjection σ n le_rfl = (awProductFst X Y).comp σ := by
      unfold simplexFrontProjection
      rw [frontSimplex_all, ContinuousMap.comp_id]
      rfl
    let project := (rawKunnethFirstProjection X Y n).comp
      (TensorProduct.map (rawFactorHomologyProjection X n) (rawFactorHomologyProjection Y 0))
    change project (rawAWComponent X Y n n 0 (Finsupp.single σ 1)) =
      rawFactorHomologyProjection X n (rawChainMap (awProductFst X Y) n (Finsupp.single σ 1))
    have hAW := rawAWComponent_single (n := n) (p := n) (q := 0) (rfl : n + 0 = n) σ 1
    calc
      _ = project (awPureTerm σ n 0 (rfl : n + 0 = n)) :=
        congrArg project (hAW.trans (one_smul ℚ _))
      _ = _ := by
        simp only [project, rawKunnethFirstProjection, LinearMap.comp_apply, awPureTerm, hfront,
          TensorProduct.map_tmul, LinearMap.id_apply, rawFullZeroAugmentation_projection, rawAugmentation_single,
          LinearEquiv.coe_coe, TensorProduct.rid_tmul, one_smul, rawChainMap,
          Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun h c

theorem rawKunnethFirstProjection_homology (n : ℕ) (a : RawHomology (X × Y) n) :
    rawKunnethFirstProjection X Y n (rawKunnethHomologyComponent X Y (rfl : n + 0 = n) a) =
      rawFullHomologyMap (awProductFst X Y) n a := by
  let c := rawHomologyCycleRepresentative (X × Y) n a
  have hc : rawFactorHomologyProjection (X × Y) n c.val = a :=
    rawFactorHomologyProjection_representative n a
  rw [← hc, rawFullHomologyMap_cycle]
  change rawKunnethFirstProjection X Y n
      (rawHomologyTensorComponent X Y (rfl : n + 0 = n)
        (rawSingularKunnethEquiv X Y n (rawFactorHomologyProjection (X × Y) n c.val))) = _
  exact (congrArg (rawKunnethFirstProjection X Y n)
    (rawKunnethChainComponent_cycle X Y (n := n) (p := n) (q := 0) (rfl : n + 0 = n) c)).trans
      (rawKunnethFirstProjection_chain X Y n c.val)

end BanachIsometric.SingularEZ
