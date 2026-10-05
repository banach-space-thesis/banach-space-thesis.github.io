import Posets.BlockScalarColumns

noncomputable section
set_option maxHeartbeats 1500000
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem fewOperators_reindex {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    {X : Q → Type*} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι) (e : P ↪o Q) :
    FewOperators 𝕜 (fun p => X (e p)) (fun s t => ι (e s) (e t)) := by
  refine ⟨fun p => h.1 (e p), ?_, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    exact h.2.1 _ _ (e.monotone hst)
  · intro r s t hrs hst
    exact h.2.2.1 _ _ _ (e.monotone hrs) (e.monotone hst)
  · intro s t hst
    exact h.2.2.2.1 _ _ (fun he => hst (e.le_iff_le.mp he))
  · intro s t hst T
    exact h.2.2.2.2.1 _ _ (e.monotone hst) T
  · intro s t hst T
    exact h.2.2.2.2.2 _ _ (fun he => hst (e.le_iff_le.mp he)) T

def fewOperatorIsometry {Q : Type*} [PartialOrder Q]
    {X : Q → Type*} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι) {s t : Q} (hst : s ≤ t) :
    X s →ₗᵢ[𝕜] X t := (ι s t).toLinearMap.toLinearIsometry (h.2.1 s t hst)

def middleOrderEmbedding (P : Type*) [PartialOrder P] : P ↪o BoundedExtension P where
  toFun := middle
  inj' := by intro s t h; simpa [middle] using h
  map_rel_iff' := by intro s t; simp [middle]

variable {P : Type*} [PartialOrder P] {X : BoundedExtension P → Type}
  [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
  {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι)

include h

theorem middleFewOperators : FewOperators 𝕜 (fun p : P => X (middle p))
    (fun s t => ι (middle s) (middle t)) := fewOperators_reindex h (middleOrderEmbedding P)

def bottomIsometry (p : P) : X ⊥ →ₗᵢ[𝕜] X (middle p) := fewOperatorIsometry h bot_le
def topIsometry (p : P) : X (middle p) →ₗᵢ[𝕜] X ⊤ := fewOperatorIsometry h le_top
def bottomTopIsometry : X ⊥ →ₗᵢ[𝕜] X ⊤ := fewOperatorIsometry h bot_le

theorem bottomIsometry_compatible {s t : P} (hst : s ≤ t) (z : X ⊥) :
    ι (middle s) (middle t) (bottomIsometry h s z) = bottomIsometry h t z :=
  congrArg (fun T : X ⊥ →L[𝕜] X (middle t) => T z)
    (h.2.2.1 ⊥ (middle s) (middle t) bot_le ((middleOrderEmbedding P).monotone hst))

theorem bottomTopIsometry_compatible (s : P) (z : X ⊥) :
    topIsometry h s (bottomIsometry h s z) = bottomTopIsometry h z :=
  congrArg (fun T : X ⊥ →L[𝕜] X ⊤ => T z)
    (h.2.2.1 ⊥ (middle s) ⊤ bot_le le_top)

theorem middleCommonSubspace : CommonSubspace 𝕜 (fun p : P => X (middle p))
    (fun s t => ι (middle s) (middle t)) :=
  ⟨X ⊥, inferInstance, inferInstance, h.1 ⊥, bottomIsometry h,
    fun _ _ hst z => bottomIsometry_compatible h hst z⟩

theorem middleBlockScalarRows
    (T : DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
      DependentCZeroSum 𝕜 (fun p : P => X (middle p))) :
    BoundedRowsOn 𝕜 (blockScalarMatrix (middleFewOperators h) T) ∧
      ∀ s, (∑' t, ‖blockScalarMatrix (middleFewOperators h) T s t‖) ≤ ‖T‖ :=
  blockScalarMatrix_boundedRows (middleFewOperators h) (middleCommonSubspace h) T

theorem middleBlockScalarColumns [Countable P]
    (T : DependentCZeroSum 𝕜 (fun p : P => X (middle p)) →L[𝕜]
      DependentCZeroSum 𝕜 (fun p : P => X (middle p))) :
    ZeroColumnsOn 𝕜 (blockScalarMatrix (middleFewOperators h) T) :=
  blockScalarMatrix_zeroColumns (middleFewOperators h) (h.1 ⊥)
    (bottomIsometry h) (topIsometry h) (bottomTopIsometry h)
    (fun _ _ hst z => bottomIsometry_compatible h hst z) (bottomTopIsometry_compatible h) T

end Posets
