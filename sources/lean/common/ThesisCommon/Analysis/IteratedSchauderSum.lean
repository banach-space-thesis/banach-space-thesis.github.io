import ThesisCommon.Analysis.SchauderSumSeries

/-! Bundled input data for the genuine finite iteration X₁(X₂(...(Xₙ))).
The innermost factor is Xₙ itself. There is no extra scalar-sum layer and no
unproved isomorphism hidden in the representation.
-/
noncomputable section
universe u v
namespace ThesisCommon

/-- A Banach space over the selected real or complex scalar field. -/
structure BanachSpaceData (𝕜 : Type u) [RCLike 𝕜] where
  Carrier : Type v
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace 𝕜 Carrier]
  [completeSpace : CompleteSpace Carrier]

attribute [instance] BanachSpaceData.normedAddCommGroup BanachSpaceData.normedSpace
  BanachSpaceData.completeSpace

/-- The basis data necessary to define a vector-valued basis sum. Symmetry
and the non-ℓ₁ hypothesis remain separate hypotheses in the paper's targets. -/
structure BasisSumFactor (𝕜 : Type u) [RCLike 𝕜] extends BanachSpaceData.{u,v} 𝕜 where
  basis : NormalizedSchauderBasis 𝕜 Carrier
  oneUnconditional : basis.IsOneUnconditional

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Recursion on a nonempty finite list of factors, with the original norm
at every level. A first factor and a tail encode exactly n>=1 factors. -/
def iteratedSchauderSum (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) : BanachSpaceData.{u,v} 𝕜 :=
  match tail with
  | [] => first.toBanachSpaceData
  | next :: rest =>
      { Carrier := SchauderSum first.basis first.oneUnconditional
          (iteratedSchauderSum next rest).Carrier }

/-- Unfolding one outer level gives the actual vector-valued sequence sum. -/
theorem iteratedSchauderSum_cons (first next : BasisSumFactor.{u,v} 𝕜)
    (rest : List (BasisSumFactor.{u,v} 𝕜)) :
    (iteratedSchauderSum first (next :: rest)).Carrier =
      SchauderSum first.basis first.oneUnconditional (iteratedSchauderSum next rest).Carrier := rfl

/-- The actual terminal product vector indexed by an n-tuple of naturals. -/
def iteratedBasisVector (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) :
    (Fin (tail.length + 1) → ℕ) → (iteratedSchauderSum first tail).Carrier :=
  match tail with
  | [] => fun t => first.basis.vector (t 0)
  | next :: rest => fun t => SchauderSum.single (b := first.basis)
      (hb := first.oneUnconditional) (t 0) (iteratedBasisVector next rest (Fin.tail t))

/-- The bounded terminal coordinate functional, composed along the actual
coordinate maps of the iterated vector-valued sum. -/
def iteratedBasisCoordinate (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) :
    (Fin (tail.length + 1) → ℕ) → (iteratedSchauderSum first tail).Carrier →L[𝕜] 𝕜 :=
  match tail with
  | [] => fun t => first.basis.coord (t 0)
  | next :: rest => fun t => (iteratedBasisCoordinate next rest (Fin.tail t)).comp
      (SchauderSum.coordinate (b := first.basis) (hb := first.oneUnconditional)
        (Y := (iteratedSchauderSum next rest).Carrier) (t 0))

theorem iteratedBasisVector_norm (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) (t : Fin (tail.length + 1) → ℕ) :
    ‖iteratedBasisVector first tail t‖ = 1 := by
  induction tail generalizing first with
  | nil => exact first.basis.norm_vector (t 0)
  | cons next rest ih =>
    change ‖SchauderSum.single (b := first.basis) (hb := first.oneUnconditional)
      (t 0) (iteratedBasisVector next rest (Fin.tail t))‖ = 1
    rw [SchauderSum.norm_single]
    exact ih next (Fin.tail t)

theorem iteratedBasisCoordinate_vector_self (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) (t : Fin (tail.length + 1) → ℕ) :
    iteratedBasisCoordinate first tail t (iteratedBasisVector first tail t) = 1 := by
  induction tail generalizing first with
  | nil => simpa using first.basis.biorthogonal (t 0) (t 0)
  | cons next rest ih =>
    change iteratedBasisCoordinate next rest (Fin.tail t)
      ((SchauderSum.single (b := first.basis) (hb := first.oneUnconditional)
        (t 0) (iteratedBasisVector next rest (Fin.tail t))) (t 0)) = 1
    rw [SchauderSum.single_apply, if_pos rfl]
    exact ih next (Fin.tail t)

end ThesisCommon
