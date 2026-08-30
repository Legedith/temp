import Mathlib

/-!
# Finite core of a correlated-amplitude Lonely Runner argument

This file contains only finite algebra, probability-as-uniform-averaging, and graph theory.
It does not claim a proof of the Lonely Runner Conjecture.

The central object is a bounded amplitude law whose distinct coordinates have zero pair moment.
A proper coloring transports such a law to graph vertices and therefore kills every quadratic
interaction supported on an edge.  We also prove the square-root obstruction showing that a law
which kills *all* distinct pairs cannot have common mean larger than `1 / sqrt(card)`.
-/

open scoped BigOperators

noncomputable section

namespace LonelyRunner

/-- Uniform average over a finite type.  It is defined to be zero on an empty type. -/
def uniformAverage {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card Ω : ℝ)

@[simp]
theorem uniformAverage_zero {Ω : Type*} [Fintype Ω] :
    uniformAverage (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [uniformAverage]

@[simp]
theorem uniformAverage_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    uniformAverage (fun _ : Ω => a) = a := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [uniformAverage, hcard]

theorem uniformAverage_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformAverage (fun ω => f ω + g ω) = uniformAverage f + uniformAverage g := by
  simp [uniformAverage, Finset.sum_add_distrib, add_div]

theorem uniformAverage_mul_left {Ω : Type*} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    uniformAverage (fun ω => a * f ω) = a * uniformAverage f := by
  unfold uniformAverage
  rw [← Finset.mul_sum]
  ring

theorem uniformAverage_mul_right {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    uniformAverage (fun ω => f ω * a) = uniformAverage f * a := by
  unfold uniformAverage
  rw [← Finset.sum_mul]
  ring

/-- A finite sum can be moved outside a uniform average. -/
theorem uniformAverage_sum {Ω ι : Type*} [Fintype Ω] (s : Finset ι) (f : ι → Ω → ℝ) :
    uniformAverage (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, uniformAverage (f i) := by
  unfold uniformAverage
  rw [Finset.sum_comm]
  rw [Finset.sum_div]

/-- A `Fintype` sum can be moved outside a uniform average. -/
theorem uniformAverage_fintypeSum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (f : ι → Ω → ℝ) :
    uniformAverage (fun ω => ∑ i, f i ω) = ∑ i, uniformAverage (f i) := by
  simpa using uniformAverage_sum (Ω := Ω) (Finset.univ : Finset ι) f

/-- Monotonicity of uniform averaging on a nonempty finite type. -/
theorem uniformAverage_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    uniformAverage f ≤ uniformAverage g := by
  have hcard : 0 < (Fintype.card Ω : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [uniformAverage, uniformAverage, div_le_div_iff_of_pos_right hcard]
  exact Finset.sum_le_sum fun ω _ => h ω

/-- The elementary Jensen/Cauchy inequality for a uniform finite average. -/
theorem sq_uniformAverage_le_uniformAverage_sq {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ) :
    (uniformAverage f) ^ 2 ≤ uniformAverage (fun ω => (f ω) ^ 2) := by
  simpa [uniformAverage] using
    (sum_div_card_sq_le_sum_sq_div_card
      (s := (Finset.univ : Finset Ω)) (f := f))

/--
A bounded finite amplitude law with common mean `α` and exact cancellation of every pair of
*distinct* coordinates.
-/
structure PairCancellingLaw (C : Type*) [Fintype C] where
  Ω : Type
  [fintypeΩ : Fintype Ω]
  [nonemptyΩ : Nonempty Ω]
  U : Ω → C → ℝ
  α : ℝ
  bounded : ∀ ω c, |U ω c| ≤ 1
  mean : ∀ c, uniformAverage (fun ω => U ω c) = α
  pair_cancel : ∀ {c d}, c ≠ d →
    uniformAverage (fun ω => U ω c * U ω d) = 0

namespace PairCancellingLaw

variable {C : Type*} [Fintype C] (L : PairCancellingLaw C)

/-- The law's common mean, transported through any map into its coordinate set. -/
theorem mean_comp {V : Type*} (color : V → C) (v : V) :
    letI := L.fintypeΩ
    uniformAverage (fun ω => L.U ω (color v)) = L.α := by
  letI := L.fintypeΩ
  exact L.mean (color v)

/-- A proper coloring transports pair cancellation from colors to graph edges. -/
theorem edge_pair_cancel {V : Type*} (G : SimpleGraph V) (color : G.Coloring C)
    {u v : V} (huv : G.Adj u v) :
    letI := L.fintypeΩ
    uniformAverage (fun ω => L.U ω (color u) * L.U ω (color v)) = 0 := by
  letI := L.fintypeΩ
  exact L.pair_cancel (color.valid huv)

/-- Multiplying an edge interaction by a deterministic weight preserves its cancellation. -/
theorem weighted_edge_pair_cancel {V : Type*} (G : SimpleGraph V) (color : G.Coloring C)
    (a : ℝ) {u v : V} (huv : G.Adj u v) :
    letI := L.fintypeΩ
    uniformAverage (fun ω => a * (L.U ω (color u) * L.U ω (color v))) = 0 := by
  letI := L.fintypeΩ
  rw [uniformAverage_mul_left, L.edge_pair_cancel G color huv, mul_zero]

/--
Every finite weighted quadratic expression supported on graph edges has zero average.  This is the
finite statement used to annihilate the harmful level-two terms of a Riesz-product expansion.
-/
theorem weighted_edge_sum_cancel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (color : G.Coloring C)
    (E : Finset (V × V)) (hE : ∀ e ∈ E, G.Adj e.1 e.2)
    (weight : V × V → ℝ) :
    letI := L.fintypeΩ
    uniformAverage (fun ω =>
      ∑ e ∈ E, weight e * (L.U ω (color e.1) * L.U ω (color e.2))) = 0 := by
  letI := L.fintypeΩ
  rw [uniformAverage_sum]
  apply Finset.sum_eq_zero
  intro e he
  exact L.weighted_edge_pair_cancel G color (weight e) (hE e he)

/-- The second moment of the sum of all coordinates is at most the number of coordinates. -/
theorem average_sum_sq_le_card [Nonempty C] :
    letI := L.fintypeΩ
    uniformAverage (fun ω => (∑ c, L.U ω c) ^ 2) ≤ (Fintype.card C : ℝ) := by
  letI := L.fintypeΩ
  letI : Nonempty L.Ω := L.nonemptyΩ
  classical
  have hexpand :
      (fun ω => (∑ c, L.U ω c) ^ 2) =
        (fun ω => ∑ c, ∑ d, L.U ω c * L.U ω d) := by
    funext ω
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
  rw [hexpand, uniformAverage_fintypeSum]
  simp_rw [uniformAverage_fintypeSum]
  calc
    (∑ c, ∑ d, uniformAverage (fun ω => L.U ω c * L.U ω d))
        ≤ ∑ c, ∑ d, if c = d then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro c _
          apply Finset.sum_le_sum
          intro d _
          by_cases hcd : c = d
          · subst d
            rw [if_pos rfl]
            calc
              uniformAverage (fun ω => L.U ω c * L.U ω c)
                  ≤ uniformAverage (fun _ : L.Ω => (1 : ℝ)) := by
                    apply uniformAverage_mono
                    intro ω
                    have hb := L.bounded ω c
                    rw [abs_le] at hb
                    nlinarith
              _ = 1 := uniformAverage_const 1
          · rw [if_neg hcd]
            rw [L.pair_cancel hcd]
    _ = (Fintype.card C : ℝ) := by simp

/-- The average of the coordinate sum is `card C * α`. -/
theorem average_sum_eq_card_mul_mean :
    letI := L.fintypeΩ
    uniformAverage (fun ω => ∑ c, L.U ω c) = (Fintype.card C : ℝ) * L.α := by
  letI := L.fintypeΩ
  rw [uniformAverage_fintypeSum]
  simp [L.mean]

/--
**Square-root barrier.**  If all distinct coordinate pairs are killed exactly, then the common mean
cannot exceed the square-root scale:

`card C * α² ≤ 1`.

This proves that the `1 / sqrt(number of colors)` loss in the cancellation construction is not a
mere artifact of its particular balanced-sign realization.
-/
theorem card_mul_mean_sq_le_one [Nonempty C] :
    (Fintype.card C : ℝ) * L.α ^ 2 ≤ 1 := by
  letI := L.fintypeΩ
  have hJ := sq_uniformAverage_le_uniformAverage_sq
    (fun ω => ∑ c, L.U ω c)
  rw [L.average_sum_eq_card_mul_mean] at hJ
  have hU := L.average_sum_sq_le_card
  have hcard : 0 < (Fintype.card C : ℝ) := by
    exact_mod_cast Fintype.card_pos
  nlinarith [hJ, hU]

end PairCancellingLaw

/-- Build a graph by declaring every supplied support to be a clique. -/
def supportConflictGraph {V : Type*} [DecidableEq V]
    (supports : Finset (Finset V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ S ∈ supports, u ∈ S ∧ v ∈ S
  symm.symm := by
    intro u v huv
    rcases huv with ⟨hne, S, hS, hu, hv⟩
    exact ⟨hne.symm, S, hS, hv, hu⟩
  loopless.irrefl := by
    intro u huu
    exact huu.1 rfl

@[simp]
theorem supportConflictGraph_adj {V : Type*} [DecidableEq V]
    (supports : Finset (Finset V)) {u v : V} :
    (supportConflictGraph supports).Adj u v ↔
      u ≠ v ∧ ∃ S ∈ supports, u ∈ S ∧ v ∈ S := Iff.rfl

/-- Two distinct vertices appearing in one declared support receive different proper colors. -/
theorem colors_distinct_on_support {V C : Type*} [DecidableEq V]
    (supports : Finset (Finset V))
    (color : (supportConflictGraph supports).Coloring C)
    {S : Finset V} (hS : S ∈ supports) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) : color u ≠ color v := by
  apply color.valid
  exact ⟨huv, S, hS, hu, hv⟩

/-- An affine amplitude built from a centered sign coordinate. -/
def affineAmplitude {Ω C : Type*} (α r : ℝ) (H : Ω → C → ℝ) : Ω → C → ℝ :=
  fun ω c => α * (1 + r * H ω c)

/-- Average of one affine amplitude coordinate. -/
theorem uniformAverage_affineAmplitude {Ω C : Type*} [Fintype Ω] [Nonempty Ω]
    (α r : ℝ) (H : Ω → C → ℝ) (c : C) :
    uniformAverage (fun ω => affineAmplitude α r H ω c) =
      α * (1 + r * uniformAverage (fun ω => H ω c)) := by
  rw [show (fun ω => affineAmplitude α r H ω c) =
      (fun ω => α + (α * r) * H ω c) by
        funext ω
        simp [affineAmplitude]
        ring]
  rw [uniformAverage_add, uniformAverage_const, uniformAverage_mul_left]
  ring

/-- Average of the product of two affine amplitude coordinates. -/
theorem uniformAverage_affineAmplitude_mul {Ω C : Type*} [Fintype Ω] [Nonempty Ω]
    (α r : ℝ) (H : Ω → C → ℝ) (c d : C) :
    uniformAverage (fun ω =>
      affineAmplitude α r H ω c * affineAmplitude α r H ω d) =
      α ^ 2 *
        (1 + r * uniformAverage (fun ω => H ω c) +
          r * uniformAverage (fun ω => H ω d) +
          r ^ 2 * uniformAverage (fun ω => H ω c * H ω d)) := by
  rw [show (fun ω =>
      affineAmplitude α r H ω c * affineAmplitude α r H ω d) =
      (fun ω => α ^ 2 +
        (α ^ 2 * r) * H ω c +
        (α ^ 2 * r) * H ω d +
        (α ^ 2 * r ^ 2) * (H ω c * H ω d)) by
          funext ω
          simp [affineAmplitude]
          ring]
  repeat' rw [uniformAverage_add]
  rw [uniformAverage_const]
  repeat' rw [uniformAverage_mul_left]
  ring

/--
The exact algebra behind the balanced-sign construction.  Zero first moments and covariance `κ`,
together with `1 + r² κ = 0`, make all distinct affine-amplitude pairs vanish.
-/
theorem affine_pair_cancel_of_centered_covariance
    {Ω C : Type*} [Fintype Ω] [Nonempty Ω]
    (α r κ : ℝ) (H : Ω → C → ℝ)
    (hmean : ∀ c, uniformAverage (fun ω => H ω c) = 0)
    (hpair : ∀ {c d}, c ≠ d →
      uniformAverage (fun ω => H ω c * H ω d) = κ)
    (hscale : 1 + r ^ 2 * κ = 0)
    {c d : C} (hcd : c ≠ d) :
    uniformAverage (fun ω =>
      affineAmplitude α r H ω c * affineAmplitude α r H ω d) = 0 := by
  rw [uniformAverage_affineAmplitude_mul, hmean c, hmean d, hpair hcd]
  rw [show 1 + r * 0 + r * 0 + r ^ 2 * κ = 1 + r ^ 2 * κ by ring]
  rw [hscale, mul_zero]

/-- Centered coordinates give affine amplitudes with common mean `α`. -/
theorem affine_mean_of_centered
    {Ω C : Type*} [Fintype Ω] [Nonempty Ω]
    (α r : ℝ) (H : Ω → C → ℝ)
    (hmean : ∀ c, uniformAverage (fun ω => H ω c) = 0)
    (c : C) :
    uniformAverage (fun ω => affineAmplitude α r H ω c) = α := by
  rw [uniformAverage_affineAmplitude, hmean c]
  ring

end LonelyRunner
