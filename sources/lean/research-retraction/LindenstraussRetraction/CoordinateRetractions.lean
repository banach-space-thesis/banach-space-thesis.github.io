import LindenstraussRetraction.C0SumCoordinates

/-! A ball retraction on the c₀-sum gives coordinate retractions with one
common modulus of continuity. No identification of the whole bidual of a
dependent c₀-sum with an ℓ∞-sum is needed. -/

noncomputable section

namespace LindenstraussRetraction

universe u v
variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : ℕ → Type u) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]
variable (F : Type u) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 200000

/-- A family of isometric coordinate insertions and contractive left inverses. -/
structure FamilyCoordinates where
  insertion : ∀ n, E n →ₗᵢ[𝕜] F
  projection : ∀ n, F →L[𝕜] E n
  bound : ∀ n x, ‖projection n x‖ ≤ ‖x‖
  leftInverse : ∀ n x, projection n (insertion n x) = x

variable {F}

def c0SumFamilyCoordinates : FamilyCoordinates 𝕜 E (C0Sum 𝕜 E) where
  insertion := c0SumSingleIsometry 𝕜 E
  projection := c0SumCoordinate 𝕜 E
  bound := fun n x => c0Sum_norm_coordinate_le 𝕜 E x n
  leftInverse := c0SumCoordinate_single 𝕜 E

variable (C : FamilyCoordinates 𝕜 E F)

def coordinateBidualBallEmbedding (n : ℕ) :
    UnitBall (Bidual 𝕜 (E n)) → UnitBall (Bidual 𝕜 F) := fun z =>
  ⟨bidualIsometry (C.insertion n) z.val, by
    simpa only [LinearIsometry.norm_map] using z.property⟩

theorem coordinateBidualBallEmbedding_isometry (n : ℕ) :
    Isometry (coordinateBidualBallEmbedding 𝕜 E C n) := by
  apply Isometry.of_dist_eq (f := coordinateBidualBallEmbedding 𝕜 E C n)
  intro a b
  change dist (bidualIsometry (C.insertion n) a.val)
    (bidualIsometry (C.insertion n) b.val) = dist a.val b.val
  exact (bidualIsometry (C.insertion n)).isometry.dist_eq _ _

def coordinateBallProjection (n : ℕ) : UnitBall F → UnitBall (E n) :=
  fun w => ⟨C.projection n w.val, (C.bound n w.val).trans w.property⟩

theorem coordinateBallProjection_dist_le (n : ℕ) (a b : UnitBall F) :
    dist (coordinateBallProjection 𝕜 E C n a) (coordinateBallProjection 𝕜 E C n b) ≤
      dist a b := by
  change dist (C.projection n a.val) (C.projection n b.val) ≤
    dist a.val b.val
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact C.bound n (a.val-b.val)

def coordinateRetraction
    (R : UnitBall (Bidual 𝕜 F) → UnitBall F) (n : ℕ) :
    UnitBall (Bidual 𝕜 (E n)) → UnitBall (E n) :=
  coordinateBallProjection 𝕜 E C n ∘ R ∘ coordinateBidualBallEmbedding 𝕜 E C n

theorem coordinateRetraction_leftInverse
    (R : UnitBall (Bidual 𝕜 F) → UnitBall F)
    (hR : IsRetraction (unitBallBidualEmbedding 𝕜 F) R) (n : ℕ) :
    IsRetraction (unitBallBidualEmbedding 𝕜 (E n)) (coordinateRetraction 𝕜 E C R n) := by
  intro x
  let wx : UnitBall F :=
    ⟨C.insertion n x.val, by simpa only [LinearIsometry.norm_map] using x.property⟩
  have he : coordinateBidualBallEmbedding 𝕜 E C n (unitBallBidualEmbedding 𝕜 (E n) x) =
      unitBallBidualEmbedding 𝕜 F wx := by
    apply Subtype.ext
    change bidualMap (C.insertion n).toContinuousLinearMap
      (bidualEmbedding 𝕜 (E n) x.val) = _
    exact bidualMap_embedding (C.insertion n).toContinuousLinearMap x.val
  change coordinateBallProjection 𝕜 E C n
    (R (coordinateBidualBallEmbedding 𝕜 E C n (unitBallBidualEmbedding 𝕜 (E n) x))) = x
  rw [he, hR wx]
  apply Subtype.ext
  exact C.leftInverse n x.val

/-- The same `δ` works for every coordinate. This is the quantitative uniform
continuity input used by the paper's contradiction. -/
theorem coordinateRetraction_common_modulus
    (R : UnitBall (Bidual 𝕜 F) → UnitBall F)
    (hR : UniformContinuous R) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n (a b : UnitBall (Bidual 𝕜 (E n))), dist a b < δ →
        dist (coordinateRetraction 𝕜 E C R n a) (coordinateRetraction 𝕜 E C R n b) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδR⟩ := (Metric.uniformContinuous_iff (f := R)).1 hR ε hε
  refine ⟨δ, hδ, fun n a b hab => ?_⟩
  apply lt_of_le_of_lt (coordinateBallProjection_dist_le 𝕜 E C n _ _)
  apply hδR
  rwa [(coordinateBidualBallEmbedding_isometry 𝕜 E C n).dist_eq]

theorem coordinateRetraction_uniformContinuous
    (R : UnitBall (Bidual 𝕜 F) → UnitBall F)
    (hR : UniformContinuous R) (n : ℕ) :
    UniformContinuous (coordinateRetraction 𝕜 E C R n) := by
  rw [Metric.uniformContinuous_iff (f := coordinateRetraction 𝕜 E C R n)]
  intro ε hε
  obtain ⟨δ, hδ, hδR⟩ := coordinateRetraction_common_modulus 𝕜 E C R hR ε hε
  exact ⟨δ, hδ, hδR n⟩

end LindenstraussRetraction
