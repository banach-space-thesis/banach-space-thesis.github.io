import BanachIsometric.ProductHigherHomotopy
import BanachIsometric.FiniteTorusCovering

/-! Projection away from an actual finite torus induces an actual group
isomorphism in degrees at least two. Combining it with an ACTUAL supplied
covering removes that torus factor from the actual homotopy group. Neither
existence of a compact-Lie-group decomposition nor semisimple homotopy torsion
is assumed or asserted by these standalone constructions. -/

noncomputable section
namespace BanachIsometric

def productLeftSubsingletonMulEquiv {G H : Type*} [Group G] [Group H] [Subsingleton G] :
    (G × H) ≃* H where
  toFun := Prod.snd
  invFun h := (1, h)
  left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def torusFactorProjectionHigherHomotopyEquiv
    {ι Y : Type*} [Fintype ι] [TopologicalSpace Y]
    (period : ι → ℝ) (hperiod : ∀ i, 0 < period i) (y : Y) (n : ℕ) :
    HomotopyGroup (Fin (n + 2)) ((∀ i, AddCircle (period i)) × Y) (0, y) ≃*
      HomotopyGroup (Fin (n + 2)) Y y := by
  letI := subsingleton_higherHomotopy_finiteTorus period hperiod n
  exact productHigherHomotopyEquiv.trans productLeftSubsingletonMulEquiv

theorem torusFactorProjectionHigherHomotopyEquiv_apply_class
    {ι Y : Type*} [Fintype ι] [TopologicalSpace Y]
    (period : ι → ℝ) (hperiod : ∀ i, 0 < period i) (y : Y) (n : ℕ)
    (α : GenLoop (Fin (n + 2)) ((∀ i, AddCircle (period i)) × Y) (0, y)) :
    torusFactorProjectionHigherHomotopyEquiv period hperiod y n (genLoopClass α) =
      genLoopClass (SphereGenerator.mapGenLoop ContinuousMap.snd rfl α) := rfl

def coveringTorusFactorHigherHomotopyEquiv
    {ι Y B : Type*} [Fintype ι] [TopologicalSpace Y] [TopologicalSpace B]
    (period : ι → ℝ) (hperiod : ∀ i, 0 < period i)
    {p : ((∀ i, AddCircle (period i)) × Y) → B} (hp : IsCoveringMap p) (y : Y) (n : ℕ) :
    HomotopyGroup (Fin (n + 2)) B (p (0, y)) ≃* HomotopyGroup (Fin (n + 2)) Y y :=
  (coveringHigherHomotopyEquiv hp (0, y) n).symm.trans
    (torusFactorProjectionHigherHomotopyEquiv period hperiod y n)

end BanachIsometric
