import BanachIsometric.ContractibleZeroHomology
import Mathlib.Topology.Connected.PathConnected

/-! Degree-zero singular homology of a genuine path-connected space is ℚ.
Every actual zero-simplex is constant, and an actual path supplies its
one-chain relation to the chosen point through the proved geometric prism.
No contractibility of the space is required. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {X : Type*} [TopologicalSpace X]

theorem simplexZero_eq_vertex (w : Simplex 0) :
    w = stdSimplex.vertex (0 : Fin 1) := by
  apply stdSimplex.ext
  funext i
  have hi : i = 0 := Fin.ext (by omega)
  subst i
  have hw : w 0 = 1 := by simpa using stdSimplex.sum_eq_one w
  simpa using hw

def zeroSimplexPathHomotopy (x : X) (σ : RawSingularSimplex X 0)
    (γ : Path x (σ (stdSimplex.vertex (0 : Fin 1)))) :
    (ContinuousMap.const (Simplex 0) x).Homotopy σ where
  toFun q := γ q.1
  continuous_toFun := γ.continuous.comp continuous_fst
  map_zero_left _ := γ.source
  map_one_left w := by
    change γ 1 = σ w
    rw [γ.target, simplexZero_eq_vertex w]

theorem rawZeroHomology_simplex_eq_point_of_path (x : X) (σ : RawSingularSimplex X 0)
    (γ : Path x (σ (stdSimplex.vertex (0 : Fin 1)))) :
    (Submodule.Quotient.mk (Finsupp.single σ (1 : ℚ)) : RawZeroHomology X) =
      rawZeroHomologyPoint x 1 := by
  let H := zeroSimplexPathHomotopy x σ γ
  change Submodule.Quotient.mk (Finsupp.single σ (1 : ℚ)) =
    Submodule.Quotient.mk (Finsupp.single (ContinuousMap.const (Simplex 0) x) (1 : ℚ))
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨rawPrism H 0 (Finsupp.single (ContinuousMap.id (Simplex 0)) 1), ?_⟩
  simpa only [ContinuousMap.comp_id] using
    rawPrism_zero_single H (ContinuousMap.id (Simplex 0))

theorem rawZeroHomology_simplex_eq_point [PathConnectedSpace X]
    (x : X) (σ : RawSingularSimplex X 0) :
    (Submodule.Quotient.mk (Finsupp.single σ (1 : ℚ)) : RawZeroHomology X) =
      rawZeroHomologyPoint x 1 :=
  rawZeroHomology_simplex_eq_point_of_path x σ (PathConnectedSpace.somePath x _)

theorem rawZeroHomologyPoint_augmentation [PathConnectedSpace X] (x : X) :
    (rawZeroHomologyPoint x).comp (rawZeroHomologyAugmentation X) = LinearMap.id := by
  have hc : (LinearMap.range (rawBoundary (X := X) 0)).mkQ =
      (rawZeroHomologyPoint x).comp (rawAugmentation X) := by
    apply Finsupp.lhom_ext
    intro σ a
    have ha : Finsupp.single σ a = a • Finsupp.single σ 1 := by simp
    rw [ha]
    simp only [map_smul]
    congr 1
    change Submodule.Quotient.mk (Finsupp.single σ (1 : ℚ)) =
      rawZeroHomologyPoint x (rawAugmentation X (Finsupp.single σ 1))
    rw [rawAugmentation_single]
    exact rawZeroHomology_simplex_eq_point x σ
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    change rawZeroHomologyPoint x (rawAugmentation X c) = Submodule.Quotient.mk c
    exact (LinearMap.congr_fun hc c).symm

def rawZeroHomologyPathConnectedEquiv [PathConnectedSpace X] (x : X) :
    RawZeroHomology X ≃ₗ[ℚ] ℚ :=
  LinearEquiv.ofLinear (rawZeroHomologyAugmentation X) (rawZeroHomologyPoint x)
    (rawZeroHomologyAugmentation_point x) (rawZeroHomologyPoint_augmentation x)

end BanachIsometric.SingularPrism
