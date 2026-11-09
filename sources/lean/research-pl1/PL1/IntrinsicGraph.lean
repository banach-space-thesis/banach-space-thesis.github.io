import PL1.Definitions

/-!
# An intrinsic norm as a closed graph in an `ℓ₁` sum

For continuous coordinate operators `D n`, the vectors of the intrinsic space
are exactly the summable tuples satisfying `x n = D n (x 0)`. The norm is the
actual inherited `ℓ₁` norm; completeness follows from closedness of these
coordinate equations. The coordinate operators themselves need not be
uniformly bounded.
-/

noncomputable section

namespace PL1.IntrinsicGraph

variable {𝕜 Y : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The ambient countable `ℓ₁` sum of copies of `Y`. -/
abbrev Ambient := lp (fun _ : ℕ => Y) 1

/-- The simultaneous graph of all coordinate operators, based at coordinate zero. -/
def graph (D : ℕ → Y →L[𝕜] Y) : Submodule 𝕜 (Ambient (Y := Y)) where
  carrier := {x | ∀ n, x n = D n (x 0)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy n
    simp only [lp.coeFn_add, Pi.add_apply, map_add, hx n, hy n]
  smul_mem' := by
    intro c x hx n
    simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, hx n]

/-- The intrinsic normed space, with the norm inherited from the actual `ℓ₁` sum. -/
abbrev Space (D : ℕ → Y →L[𝕜] Y) := graph D

variable (D : ℕ → Y →L[𝕜] Y)

@[simp]
theorem mem_graph (x : Ambient (Y := Y)) :
    x ∈ graph D ↔ ∀ n, x n = D n (x 0) := Iff.rfl

/-- Each defining coordinate equation is closed. -/
theorem isClosed_graph : IsClosed (graph D : Set (Ambient (Y := Y))) := by
  change IsClosed {x : Ambient (Y := Y) | ∀ n, x n = D n (x 0)}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro n
  exact isClosed_eq (lp.evalCLM 𝕜 (fun _ : ℕ => Y) 1 n).continuous
    ((D n).continuous.comp (lp.evalCLM 𝕜 (fun _ : ℕ => Y) 1 0).continuous)

instance [CompleteSpace Y] : CompleteSpace (Space D) :=
  (isClosed_graph D).isComplete.completeSpace_coe

/-- The canonical embedding into the ambient sum is isometric. -/
def inclusion : Space D →ₗᵢ[𝕜] Ambient (Y := Y) :=
  (graph D).subtypeₗᵢ

/-- Evaluation at any coordinate of the intrinsic graph is continuous linear. -/
def coord (n : ℕ) : Space D →L[𝕜] Y :=
  (lp.evalCLM 𝕜 (fun _ : ℕ => Y) 1 n).comp (graph D).subtypeL

@[simp]
theorem coord_apply (n : ℕ) (x : Space D) :
    coord D n x = (x : Ambient (Y := Y)) n := rfl

/-- Coordinate zero recovers the original underlying vector. -/
def evalZero : Space D →L[𝕜] Y := coord D 0

@[simp]
theorem evalZero_apply (x : Space D) :
    evalZero D x = (x : Ambient (Y := Y)) 0 := rfl

theorem coord_eq (n : ℕ) (x : Space D) :
    coord D n x = D n (evalZero D x) := x.property n

/-- The zeroth coordinate determines the whole intrinsic graph vector. -/
theorem evalZero_injective : Function.Injective (evalZero D) := by
  intro x y h
  apply Subtype.ext
  apply lp.ext
  funext n
  change coord D n x = coord D n y
  rw [coord_eq, coord_eq, h]

/-- The original ambient norm is bounded by the intrinsic graph norm. -/
theorem norm_evalZero_le (x : Space D) : ‖evalZero D x‖ ≤ ‖x‖ := by
  exact lp.norm_apply_le_norm (by simp) (x : Ambient (Y := Y)) 0

theorem opNorm_evalZero_le_one : ‖evalZero D‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using norm_evalZero_le D x

/-- The graph norm is precisely the sum of the coordinate norms. -/
theorem norm_eq_tsum (x : Space D) :
    ‖x‖ = ∑' n : ℕ, ‖coord D n x‖ := by
  change ‖(x : Ambient (Y := Y))‖ = ∑' n : ℕ, ‖(x : Ambient (Y := Y)) n‖
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)
    (x : Ambient (Y := Y))

theorem norm_eq_tsum_operators (x : Space D) :
    ‖x‖ = ∑' n : ℕ, ‖D n (evalZero D x)‖ := by
  rw [norm_eq_tsum]
  congr 1
  funext n
  rw [coord_eq]

/-- A vector belongs to the intrinsic space whenever its operator coordinates
are absolutely summable, provided coordinate zero is the identity. -/
def ofSummable (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
    (f : Y) (hf : Summable (fun n : ℕ => ‖D n f‖)) : Space D :=
  ⟨⟨fun n => D n f, memℓp_gen (by simpa using hf)⟩, by
    intro n
    change D n f = D n (D 0 f)
    rw [h0]
    rfl⟩

@[simp]
theorem coord_ofSummable (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
    (f : Y) (hf : Summable (fun n : ℕ => ‖D n f‖)) (n : ℕ) :
    coord D n (ofSummable D h0 f hf) = D n f := rfl

@[simp]
theorem evalZero_ofSummable (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
    (f : Y) (hf : Summable (fun n : ℕ => ‖D n f‖)) :
    evalZero D (ofSummable D h0 f hf) = f := by
  change D 0 f = f
  rw [h0]
  rfl

theorem norm_ofSummable (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
    (f : Y) (hf : Summable (fun n : ℕ => ‖D n f‖)) :
    ‖ofSummable D h0 f hf‖ = ∑' n : ℕ, ‖D n f‖ := by
  rw [norm_eq_tsum]
  rfl

/-- Scalar recovery identifies the graph exactly with the vectors having
finite intrinsic norm, rather than only embedding a subset of them. -/
theorem mem_range_evalZero_iff (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y) (f : Y) :
    f ∈ (evalZero D).range ↔ Summable (fun n : ℕ => ‖D n f‖) := by
  constructor
  · rintro ⟨x, rfl⟩
    change Summable (fun n : ℕ => ‖D n (evalZero D x)‖)
    have hx : Summable (fun n : ℕ => ‖coord D n x‖) := by
      simpa only [coord_apply, ENNReal.toReal_one, Real.rpow_one] using
        (lp.memℓp (x : Ambient (Y := Y))).summable (by norm_num)
    simpa only [coord_eq] using hx
  · intro hf
    exact ⟨ofSummable D h0 f hf, evalZero_ofSummable D h0 f hf⟩

/-- A smoothing operator gives an algebraic column into the intrinsic graph. -/
def columnLinear (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
    (B : Y →L[𝕜] Y)
    (hs : ∀ y : Y, Summable (fun n : ℕ => ‖D n (B y)‖)) :
    Y →ₗ[𝕜] Space D where
  toFun y := ofSummable D h0 (B y) (hs y)
  map_add' x y := by
    apply Subtype.ext
    apply lp.ext
    funext n
    change D n (B (x + y)) = D n (B x) + D n (B y)
    simp only [map_add]
  map_smul' c y := by
    apply Subtype.ext
    apply lp.ext
    funext n
    change D n (B (c • y)) = c • D n (B y)
    simp only [map_smul]

/-- A uniform estimate on the sum of coordinate norms bundles the smoothing
column as a bounded operator into the intrinsic Banach space. -/
def column (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
    (B : Y →L[𝕜] Y)
    (hs : ∀ y : Y, Summable (fun n : ℕ => ‖D n (B y)‖))
    (C : ℝ) (hC : ∀ y : Y, (∑' n : ℕ, ‖D n (B y)‖) ≤ C * ‖y‖) :
    Y →L[𝕜] Space D :=
  (columnLinear D h0 B hs).mkContinuous C (fun y => by
    change ‖ofSummable D h0 (B y) (hs y)‖ ≤ C * ‖y‖
    rw [norm_ofSummable]
    exact hC y)

@[simp]
theorem column_apply (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
    (B : Y →L[𝕜] Y)
    (hs : ∀ y : Y, Summable (fun n : ℕ => ‖D n (B y)‖))
    (C : ℝ) (hC : ∀ y : Y, (∑' n : ℕ, ‖D n (B y)‖) ≤ C * ‖y‖) (y : Y) :
    column D h0 B hs C hC y = ofSummable D h0 (B y) (hs y) := rfl

theorem norm_column_le (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
    (B : Y →L[𝕜] Y)
    (hs : ∀ y : Y, Summable (fun n : ℕ => ‖D n (B y)‖))
    (C : ℝ) (hC : ∀ y : Y, (∑' n : ℕ, ‖D n (B y)‖) ≤ C * ‖y‖)
    (hC0 : 0 ≤ C) : ‖column D h0 B hs C hC‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC0
  intro y
  rw [column_apply, norm_ofSummable]
  exact hC y

@[simp]
theorem evalZero_column (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
    (B : Y →L[𝕜] Y)
    (hs : ∀ y : Y, Summable (fun n : ℕ => ‖D n (B y)‖))
    (C : ℝ) (hC : ∀ y : Y, (∑' n : ℕ, ‖D n (B y)‖) ≤ C * ‖y‖) (y : Y) :
    evalZero D (column D h0 B hs C hC y) = B y := by
  rw [column_apply, evalZero_ofSummable]

end PL1.IntrinsicGraph
