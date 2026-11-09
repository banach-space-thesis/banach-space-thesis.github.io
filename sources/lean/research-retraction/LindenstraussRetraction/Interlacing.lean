import LindenstraussRetraction.Stability
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Iterated ultrafilter limits of the ℓ₁ distance kernel

The limit types below permit the interlacing argument without constructing
the Johnson–Zippin space or introducing an external obstruction axiom.
-/

noncomputable section

open Filter Topology TopologicalSpace
open scoped NNReal ENNReal

namespace LindenstraussRetraction

universe u v w

variable {I : Type u} {B : I → Type v} [∀ i, NormedAddCommGroup (B i)]

/-- A distance type of an ℓ₁ sum: its point and total limiting norm. -/
structure L1MetricType (B : I → Type v) [∀ i, NormedAddCommGroup (B i)] where
  point : lp B 1
  mass : ℝ
  norm_le_mass : ‖point‖ ≤ mass

namespace L1MetricType

def ofPoint (x : lp B 1) : L1MetricType B := ⟨x, ‖x‖, le_refl _⟩

/-- The separately continuous extension of the distance kernel. The radius
of a type is `mass - ‖point‖`. -/
def distance (x y : L1MetricType B) : ℝ :=
  ‖x.point - y.point‖ + (x.mass - ‖x.point‖) + (y.mass - ‖y.point‖)

theorem distance_nonneg (x y : L1MetricType B) : 0 ≤ x.distance y := by
  dsimp [distance]
  linarith [norm_nonneg (x.point - y.point), x.norm_le_mass, y.norm_le_mass]

theorem distance_symm (x y : L1MetricType B) : x.distance y = y.distance x := by
  dsimp [distance]
  rw [norm_sub_rev]
  ring

@[simp] theorem distance_ofPoint (x y : lp B 1) :
    (ofPoint x).distance (ofPoint y) = ‖x - y‖ := by simp [distance, ofPoint]

/-- Bounded type families admit a limit preserving the distance to every
fixed type. This is the form used while interchanging interlaced limits. -/
theorem exists_limit [∀ i, ProperSpace (B i)] {A : Type w}
    (U : Ultrafilter A) (F : A → L1MetricType B)
    {C : ℝ} (hC : ∀ a, (F a).mass ≤ C) :
    ∃ t : L1MetricType B, t.mass ≤ C ∧
      ∀ y : L1MetricType B, Tendsto (fun a => (F a).distance y) U (𝓝 (t.distance y)) := by
  obtain ⟨x, _, hx⟩ := l1_exists_ultrafilter_coordinate_limit U (fun a => (F a).point)
    (fun a => (F a).norm_le_mass.trans (hC a))
  obtain ⟨b, hb, hb_lim⟩ := isCompact_Icc.ultrafilter_le_nhds
    (U.map (fun a => (F a).mass)) (by
      rw [le_principal_iff]
      change ∀ᶠ a in (U : Filter A), (F a).mass ∈ Set.Icc 0 C
      exact Eventually.of_forall (fun a =>
        ⟨(norm_nonneg (F a).point).trans (F a).norm_le_mass, hC a⟩))
  have hlim (y : lp B 1) : Tendsto
      (fun a => ‖(F a).point - y‖ - ‖(F a).point‖ + (F a).mass)
      U (𝓝 (‖x - y‖ - ‖x‖ + b)) := by
    simpa only [← sub_eq_add_neg] using (l1_tendsto_norm_add_sub_norm hx (-y)).add hb_lim
  have hxb : ‖x‖ ≤ b := by
    have h : 0 ≤ ‖x - x‖ - ‖x‖ + b := ge_of_tendsto (hlim x) (Eventually.of_forall (fun a => by
      have hm := (F a).norm_le_mass
      have hn := norm_nonneg ((F a).point - x)
      linarith))
    simp only [sub_self, norm_zero] at h
    linarith
  refine ⟨⟨x, b, hxb⟩, hb.2, fun y => ?_⟩
  have h := (hlim y.point).add_const (y.mass - ‖y.point‖)
  convert h using 1
  · ext a
    dsimp [distance]
    ring
  · congr 1
    dsimp [distance]
    ring

end L1MetricType

namespace L1MetricType

variable [∀ i, ProperSpace (B i)]

/-- Choose the distance-kernel limit of a mass-bounded family. -/
def boundedLimit {A : Type w} (U : Ultrafilter A) (C : ℝ)
    (F : A → L1MetricType B) : L1MetricType B := by
  classical
  exact if h : ∀ a, (F a).mass ≤ C then Classical.choose (exists_limit U F h) else ofPoint 0

theorem boundedLimit_mass {A : Type w} (U : Ultrafilter A) (C : ℝ)
    (F : A → L1MetricType B) (h : ∀ a, (F a).mass ≤ C) :
    (boundedLimit U C F).mass ≤ C := by
  classical
  rw [boundedLimit, dif_pos h]
  exact (Classical.choose_spec (exists_limit U F h)).1

theorem boundedLimit_distance {A : Type w} (U : Ultrafilter A) (C : ℝ)
    (F : A → L1MetricType B) (h : ∀ a, (F a).mass ≤ C) (y : L1MetricType B) :
    Tendsto (fun a => (F a).distance y) U (𝓝 ((boundedLimit U C F).distance y)) := by
  classical
  rw [boundedLimit, dif_pos h]
  exact (Classical.choose_spec (exists_limit U F h)).2 y

/-- Eliminate the variables of a finite array in their original order. -/
def iteratedLimit (U : Ultrafilter ℕ) (C : ℝ) :
    (k : ℕ) → ((Fin k → ℕ) → L1MetricType B) → L1MetricType B
  | 0, F => F (fun i => Fin.elim0 i)
  | k + 1, F => boundedLimit U C
      (fun n => iteratedLimit U C k (fun v => F (Fin.cons n v)))

theorem iteratedLimit_mass (U : Ultrafilter ℕ) (C : ℝ)
    (k : ℕ) (F : (Fin k → ℕ) → L1MetricType B) (h : ∀ v, (F v).mass ≤ C) :
    (iteratedLimit U C k F).mass ≤ C := by
  induction k with
  | zero => exact h _
  | succ k ih =>
    exact boundedLimit_mass U C _ (fun n => ih _ (fun v => h (Fin.cons n v)))

/-- Alternately eliminate one variable from each of the two arrays. -/
def alternatingDistanceLimit (U : Ultrafilter ℕ) :
    (k : ℕ) → ((Fin k → ℕ) → L1MetricType B) →
      ((Fin k → ℕ) → L1MetricType B) → ℝ
  | 0, F, G => (F (fun i => Fin.elim0 i)).distance (G (fun i => Fin.elim0 i))
  | k + 1, F, G => limUnder (U : Filter ℕ) (fun n =>
      limUnder (U : Filter ℕ) (fun m =>
        alternatingDistanceLimit U k
          (fun v => F (Fin.cons n v)) (fun v => G (Fin.cons m v))))

/-- Interlacing the ultrafilter limits gives the same value as eliminating
all left variables and then all right variables. -/
theorem alternatingDistanceLimit_eq (U : Ultrafilter ℕ) (C : ℝ)
    (k : ℕ) (F G : (Fin k → ℕ) → L1MetricType B)
    (hF : ∀ v, (F v).mass ≤ C) (hG : ∀ v, (G v).mass ≤ C) :
    alternatingDistanceLimit U k F G =
      (iteratedLimit U C k F).distance (iteratedLimit U C k G) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let FL := fun n => iteratedLimit U C k (fun v => F (Fin.cons n v))
    let GL := fun m => iteratedLimit U C k (fun v => G (Fin.cons m v))
    have hFL : ∀ n, (FL n).mass ≤ C :=
      fun n => iteratedLimit_mass U C k _ (fun v => hF (Fin.cons n v))
    have hGL : ∀ m, (GL m).mass ≤ C :=
      fun m => iteratedLimit_mass U C k _ (fun v => hG (Fin.cons m v))
    have hinner (n : ℕ) : Tendsto
        (fun m => alternatingDistanceLimit U k
          (fun v => F (Fin.cons n v)) (fun v => G (Fin.cons m v)))
        U (𝓝 ((FL n).distance (boundedLimit U C GL))) := by
      have h := boundedLimit_distance U C GL hGL (FL n)
      rw [distance_symm (boundedLimit U C GL) (FL n)] at h
      simp only [distance_symm (GL _) (FL n)] at h
      convert h using 1
      ext m
      exact ih _ _ (fun v => hF (Fin.cons n v)) (fun v => hG (Fin.cons m v))
    change limUnder (U : Filter ℕ) _ =
      (boundedLimit U C FL).distance (boundedLimit U C GL)
    have houter := boundedLimit_distance U C FL hFL (boundedLimit U C GL)
    have heq : (fun n => limUnder (U : Filter ℕ) (fun m =>
        alternatingDistanceLimit U k
          (fun v => F (Fin.cons n v)) (fun v => G (Fin.cons m v)))) =
        (fun n => (FL n).distance (boundedLimit U C GL)) := by
      funext n
      exact (hinner n).limUnder_eq
    rw [heq]
    exact houter.limUnder_eq

end L1MetricType

/-- The variables of a finite tuple are chosen successively above a cutoff. -/
def IncreasingAfter : (k : ℕ) → ℕ → (Fin k → ℕ) → Prop
  | 0, _, _ => True
  | k + 1, N, v => N ≤ v 0 ∧ IncreasingAfter k (v 0 + 1) (fun i => v i.succ)

theorem IncreasingAfter.all_ge {k N : ℕ} {v : Fin k → ℕ}
    (h : IncreasingAfter k N v) (i : Fin k) : N ≤ v i := by
  induction k generalizing N with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases h.1 (fun j => ?_) i
    exact h.1.trans ((Nat.le_succ (v 0)).trans (ih h.2 j))

theorem IncreasingAfter.strictMono {k N : ℕ} {v : Fin k → ℕ}
    (h : IncreasingAfter k N v) : StrictMono v := by
  induction k generalizing N with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
    intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j' => ?_) j
      · intro hij; exact (lt_irrefl (0 : Fin (k + 1)) hij).elim
      · intro _; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (v 0)) (h.2.all_ge j')
    · intro j
      refine Fin.cases ?_ (fun j' => ?_) j
      · intro hij; exact (not_lt_of_ge (Fin.zero_le i'.succ) hij).elim
      · intro hij; exact ih h.2 (by simpa only [Fin.succ_lt_succ_iff] using hij)

/-- Iterated real ultrafilter limits, with one variable eliminated at a time. -/
def scalarIteratedLimit (U : Ultrafilter ℕ) : (k : ℕ) → ((Fin k → ℕ) → ℝ) → ℝ
  | 0, f => f (fun i => Fin.elim0 i)
  | k + 1, f => limUnder (U : Filter ℕ)
      (fun n => scalarIteratedLimit U k (fun v => f (Fin.cons n v)))

theorem scalar_ultrafilter_tendsto (U : Ultrafilter ℕ)
    (f : ℕ → ℝ) {a b : ℝ} (h : ∀ n, f n ∈ Set.Icc a b) :
    Tendsto f U (𝓝 (limUnder (U : Filter ℕ) f)) ∧
      limUnder (U : Filter ℕ) f ∈ Set.Icc a b := by
  obtain ⟨x, hx, hlim⟩ := isCompact_Icc.ultrafilter_le_nhds (U.map f) (by
    rw [le_principal_iff]
    change ∀ᶠ n in (U : Filter ℕ), f n ∈ Set.Icc a b
    exact Eventually.of_forall h)
  have heq := (show Tendsto f U (𝓝 x) from hlim).limUnder_eq
  exact ⟨by rwa [heq], by rwa [heq]⟩

theorem scalarIteratedLimit_mem_Icc (U : Ultrafilter ℕ) (k : ℕ)
    (f : (Fin k → ℕ) → ℝ) {a b : ℝ} (h : ∀ v, f v ∈ Set.Icc a b) :
    scalarIteratedLimit U k f ∈ Set.Icc a b := by
  induction k with
  | zero => exact h _
  | succ k ih => exact (scalar_ultrafilter_tendsto U _
      (fun n => ih _ (fun v => h (Fin.cons n v)))).2

/-- An inequality on all increasing tuples passes to the iterated limit.
Only eventual ordering is needed; no Ramsey theorem enters this step. -/
theorem scalarIteratedLimit_le_of_increasing (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (k : ℕ)
    (f : (Fin k → ℕ) → ℝ) {a b d : ℝ} (hbound : ∀ v, f v ∈ Set.Icc a b)
    (N : ℕ) (h : ∀ v, IncreasingAfter k N v → f v ≤ d) :
    scalarIteratedLimit U k f ≤ d := by
  induction k generalizing N with
  | zero => exact h _ trivial
  | succ k ih =>
    have hlim := (scalar_ultrafilter_tendsto U
      (fun n => scalarIteratedLimit U k (fun v => f (Fin.cons n v)))
      (fun n => scalarIteratedLimit_mem_Icc U k _ (fun v => hbound (Fin.cons n v)))).1
    apply le_of_tendsto hlim
    filter_upwards [(eventually_ge_atTop N).filter_mono hU] with n hn
    exact ih _ (fun v => hbound (Fin.cons n v)) (n + 1) (fun v hv =>
      h (Fin.cons n v) ⟨hn, by simpa only [Fin.cons_zero, Fin.cons_succ] using hv⟩)

/-- The corresponding lower bound for an increasing family. -/
theorem scalarIteratedLimit_ge_of_increasing (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (k : ℕ)
    (f : (Fin k → ℕ) → ℝ) {a b d : ℝ} (hbound : ∀ v, f v ∈ Set.Icc a b)
    (N : ℕ) (h : ∀ v, IncreasingAfter k N v → d ≤ f v) :
    d ≤ scalarIteratedLimit U k f := by
  induction k generalizing N with
  | zero => exact h _ trivial
  | succ k ih =>
    have hlim := (scalar_ultrafilter_tendsto U
      (fun n => scalarIteratedLimit U k (fun v => f (Fin.cons n v)))
      (fun n => scalarIteratedLimit_mem_Icc U k _ (fun v => hbound (Fin.cons n v)))).1
    apply ge_of_tendsto hlim
    filter_upwards [(eventually_ge_atTop N).filter_mono hU] with n hn
    exact ih _ (fun v => hbound (Fin.cons n v)) (n + 1) (fun v hv =>
      h (Fin.cons n v) ⟨hn, by simpa only [Fin.cons_zero, Fin.cons_succ] using hv⟩)

namespace L1MetricType

variable [∀ i, ProperSpace (B i)]

omit [∀ i, ProperSpace (B i)] in
theorem distance_le_mass (x y : L1MetricType B) : x.distance y ≤ x.mass + y.mass := by
  dsimp [distance]
  linarith [norm_sub_le x.point y.point]

/-- The scalar iterated limit against a fixed type is the extended distance
from the iterated type limit. -/
theorem scalarIteratedLimit_distance_eq (U : Ultrafilter ℕ) (C : ℝ)
    (k : ℕ) (F : (Fin k → ℕ) → L1MetricType B)
    (hF : ∀ v, (F v).mass ≤ C) (y : L1MetricType B) :
    scalarIteratedLimit U k (fun v => (F v).distance y) =
      (iteratedLimit U C k F).distance y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change limUnder (U : Filter ℕ) _ = _
    have heq : (fun n => scalarIteratedLimit U k (fun v => (F (Fin.cons n v)).distance y)) =
        (fun n => (iteratedLimit U C k (fun v => F (Fin.cons n v))).distance y) := by
      funext n
      exact ih _ (fun v => hF (Fin.cons n v))
    rw [heq]
    exact (boundedLimit_distance U C _
      (fun n => iteratedLimit_mass U C k _ (fun v => hF (Fin.cons n v))) y).limUnder_eq

end L1MetricType

/-- The even coordinates of a tuple of twice the length. -/
def evenCoordinates (k : ℕ) (v : Fin (2 * k) → ℕ) : Fin k → ℕ :=
  fun i => v ⟨2 * i.val, by omega⟩

/-- The odd coordinates of a tuple of twice the length. -/
def oddCoordinates (k : ℕ) (v : Fin (2 * k) → ℕ) : Fin k → ℕ :=
  fun i => v ⟨2 * i.val + 1, by omega⟩

theorem evenCoordinates_cons_cons (k n m : ℕ) (v : Fin (2 * k) → ℕ) :
    evenCoordinates (k + 1) (Fin.cons n (Fin.cons m v)) =
      Fin.cons n (evenCoordinates k v) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change ((Fin.cons n (Fin.cons m v)) : Fin (2 * (k + 1)) → ℕ)
      ⟨2 * (j.val + 1), _⟩ = evenCoordinates k v j
    have heq : (⟨2 * (j.val + 1), by omega⟩ : Fin (2 * (k + 1))) =
        (⟨2 * j.val, by omega⟩ : Fin (2 * k)).succ.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [heq, Fin.cons_succ, Fin.cons_succ]
    rfl

theorem oddCoordinates_cons_cons (k n m : ℕ) (v : Fin (2 * k) → ℕ) :
    oddCoordinates (k + 1) (Fin.cons n (Fin.cons m v)) =
      Fin.cons m (oddCoordinates k v) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change ((Fin.cons n (Fin.cons m v)) : Fin (2 * (k + 1)) → ℕ)
      ⟨2 * (j.val + 1) + 1, _⟩ = oddCoordinates k v j
    have heq : (⟨2 * (j.val + 1) + 1, by omega⟩ : Fin (2 * (k + 1))) =
        (⟨2 * j.val + 1, by omega⟩ : Fin (2 * k)).succ.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [heq, Fin.cons_succ, Fin.cons_succ]
    rfl

namespace L1MetricType

variable [∀ i, ProperSpace (B i)]

/-- The alternating scalar kernel in a single tuple of length `2*k`. -/
def alternatingKernel (k : ℕ) (F G : (Fin k → ℕ) → L1MetricType B)
    (v : Fin (2 * k) → ℕ) : ℝ :=
  (F (evenCoordinates k v)).distance (G (oddCoordinates k v))

omit [∀ i, ProperSpace (B i)] in
theorem scalarIteratedLimit_alternatingKernel (U : Ultrafilter ℕ) (k : ℕ)
    (F G : (Fin k → ℕ) → L1MetricType B) :
    scalarIteratedLimit U (2 * k) (alternatingKernel k F G) =
      alternatingDistanceLimit U k F G := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change limUnder (U : Filter ℕ) (fun n => limUnder (U : Filter ℕ)
      (fun m => scalarIteratedLimit U (2 * k)
        (fun v => alternatingKernel (k + 1) F G (Fin.cons n (Fin.cons m v))))) = _
    rw [alternatingDistanceLimit]
    congr 1
    funext n
    congr 1
    funext m
    have heq : (fun v => alternatingKernel (k + 1) F G (Fin.cons n (Fin.cons m v))) =
      alternatingKernel k (fun v => F (Fin.cons n v)) (fun v => G (Fin.cons m v)) := by
      funext v
      simp only [alternatingKernel, evenCoordinates_cons_cons, oddCoordinates_cons_cons]
    exact (congrArg (scalarIteratedLimit U (2 * k)) heq).trans (ih _ _)

end L1MetricType

end LindenstraussRetraction
