module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Int.Interval

/-!
# Edge retention in a one-zero lattice model of the windowed trace

A model, not a statement of the paper. It concerns the comparison that the proof of
Theorem 12.5.1.1, pp. 519–520, needs between two limits: Theorem 11.2.1.2, p. 488, removes the
Paley–Wiener level at a fixed position cutoff, while Theorem 12.4.1.1, p. 514, removes level and
cutoff together (ERRATA M25: §12.3 is missing).

The model is `ℓ²(ℤ)` with weight `w n = exp (2 α |n|)`, the lattice analogue of the strip of
half-width `α`. The level-`R` generators are `e_j - c • e_(j+1)` for `-R ≤ j ≤ R`. Their symbol
`1 - c ζ⁻¹` has its only zero at `ζ = c`, and `exp α < ‖c‖` puts that zero outside the window, at
distance `log ‖c‖ - α`. Inside the window `[-R, R + 1]` the `w`-orthogonal complement of the
generators is the line spanned by `g m = conj c ^ (-m) / w m`, whose weighted mass at `m` is
`edgeRetentionMass α ‖c‖ m` and concentrates at the edge `m = -R`.

For a convolution by `φ` supported on the lags `1, …, D`, the compression to `g` is the quotient
in `edgeRetention_compression_limits`. With no position cutoff it tends to the full contribution
`∑ φ d * c ^ (-d)` of the zero. With any fixed position cutoff it tends to `0`. So the two orders
of limit differ by exactly the term of the zero outside the window, and that term is carried by a
vector at the edge of the level. Nothing in the model depends on where the zero comes from.
-/

open Filter Topology Finset

public noncomputable section
namespace RiemannMasullo

/-- Weighted mass at the site `m` of the edge vector `g m = conj c ^ (-m) / w m` with `r = ‖c‖`
and `w m = exp (2 α |m|)`: it is `‖g m‖² w m`. A model; not a definition of the paper. -/
def edgeRetentionMass (α r : ℝ) (m : ℤ) : ℝ :=
  r ^ (-2 * m) * Real.exp (-2 * α * |(m : ℝ)|)

/-- Squared weighted norm of the edge vector on the level window `[-R, R + 1]`. -/
def edgeRetentionTotal (α r : ℝ) (R : ℕ) : ℝ :=
  ∑ m ∈ Icc (-(R : ℤ)) (R + 1), edgeRetentionMass α r m

/-- The edge mass is positive at every site. -/
theorem edgeRetentionMass_pos {α r : ℝ} (hr : 0 < r) (m : ℤ) : 0 < edgeRetentionMass α r m :=
  mul_pos (zpow_pos hr _) (Real.exp_pos _)

/-- At the left edge `m = -R` the mass is `((r exp (-α))²) ^ R`. -/
theorem edgeRetentionMass_neg_natCast (α r : ℝ) (R : ℕ) :
    edgeRetentionMass α r (-(R : ℤ)) = ((r * Real.exp (-α)) ^ 2) ^ R := by
  unfold edgeRetentionMass
  have h1 : (-2 * -(R : ℤ)) = ((2 * R : ℕ) : ℤ) := by push_cast; ring
  have h2 : |((-(R : ℤ) : ℤ) : ℝ)| = (R : ℝ) := by
    push_cast; rw [abs_neg]; exact abs_of_nonneg (Nat.cast_nonneg R)
  rw [h1, zpow_natCast, h2, ← pow_mul, mul_pow, ← Real.exp_nat_mul]
  congr 2; push_cast; ring

/-- To the right of the origin the edge mass is at most one, when `1 ≤ r` and `0 ≤ α`. -/
theorem edgeRetentionMass_le_one {α r : ℝ} (hα : 0 ≤ α) (hr : 1 ≤ r) {m : ℤ} (hm : 0 ≤ m) :
    edgeRetentionMass α r m ≤ 1 := by
  unfold edgeRetentionMass
  have h1 : r ^ (-2 * m) ≤ 1 := zpow_le_one_of_nonpos₀ hr (by omega)
  have h2 : Real.exp (-2 * α * |(m : ℝ)|) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg (m : ℝ)]
  exact (mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one).trans_eq (one_mul 1)

/-- When the zero lies outside the window (`exp α < r`), the norm of the edge vector on the level
window tends to infinity with the level: the mass sits at the edge. -/
theorem edgeRetentionTotal_tendsto {α r : ℝ} (hr : Real.exp α < r) :
    Tendsto (edgeRetentionTotal α r) atTop atTop := by
  have hr0 : 0 < r := lt_trans (Real.exp_pos α) hr
  have hq : 1 < r * Real.exp (-α) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, one_lt_div (Real.exp_pos α)]; exact hr
  have hq2 : 1 < (r * Real.exp (-α)) ^ 2 := one_lt_pow₀ hq two_ne_zero
  refine tendsto_atTop_mono (fun R => ?_) (tendsto_pow_atTop_atTop_of_one_lt hq2)
  rw [← edgeRetentionMass_neg_natCast]
  exact Finset.single_le_sum (f := edgeRetentionMass α r)
    (fun m _ => (edgeRetentionMass_pos hr0 m).le) (Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩)

/-- With no position cutoff, the share of the edge mass whose translate by the lag `d` stays in
the level window tends to one. -/
theorem edgeRetention_uncut {α r : ℝ} (hα : 0 ≤ α) (hr : Real.exp α < r) (d : ℕ) :
    Tendsto (fun R : ℕ =>
      (∑ m ∈ (Icc (-(R : ℤ)) (R + 1)).filter (fun m => m + (d : ℤ) ∈ Icc (-(R : ℤ)) (R + 1)),
        edgeRetentionMass α r m) / edgeRetentionTotal α r R) atTop (𝓝 1) := by
  have hr0 : 0 < r := lt_trans (Real.exp_pos α) hr
  have hr1 : 1 ≤ r := le_trans (Real.one_le_exp hα) hr.le
  have htot := edgeRetentionTotal_tendsto hr
  have hpos : ∀ᶠ R : ℕ in atTop, 0 < edgeRetentionTotal α r R := htot.eventually_gt_atTop 0
  -- lost mass
  let lost : ℕ → ℝ := fun R =>
    ∑ m ∈ (Icc (-(R : ℤ)) (R + 1)).filter (fun m => ¬ (m + (d : ℤ) ∈ Icc (-(R : ℤ)) (R + 1))),
      edgeRetentionMass α r m
  have hlost0 : ∀ R, 0 ≤ lost R := fun R =>
    Finset.sum_nonneg (fun m _ => (edgeRetentionMass_pos hr0 m).le)
  have hlostd : ∀ᶠ R : ℕ in atTop, lost R ≤ d := by
    filter_upwards [eventually_ge_atTop d] with R hR
    have hsub : (Icc (-(R : ℤ)) (R + 1)).filter (fun m => ¬ (m + (d : ℤ) ∈ Icc (-(R : ℤ)) (R + 1)))
        ⊆ Ioc ((R : ℤ) + 1 - (d : ℤ)) ((R : ℤ) + 1) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, not_and, not_le] at hm ⊢
      omega
    calc lost R ≤ ∑ m ∈ Ioc ((R : ℤ) + 1 - (d : ℤ)) ((R : ℤ) + 1), edgeRetentionMass α r m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun m _ _ => (edgeRetentionMass_pos hr0 m).le)
      _ ≤ ∑ _m ∈ Ioc ((R : ℤ) + 1 - (d : ℤ)) ((R : ℤ) + 1), (1 : ℝ) := by
          refine Finset.sum_le_sum (fun m hm => edgeRetentionMass_le_one hα hr1 ?_)
          simp only [Finset.mem_Ioc] at hm; omega
      _ = d := by simp [Int.card_Ioc]
  have hsplit : ∀ R : ℕ,
      (∑ m ∈ (Icc (-(R : ℤ)) (R + 1)).filter (fun m => m + (d : ℤ) ∈ Icc (-(R : ℤ)) (R + 1)),
        edgeRetentionMass α r m) = edgeRetentionTotal α r R - lost R := by
    intro R
    have := Finset.sum_filter_add_sum_filter_not (Icc (-(R : ℤ)) (R + 1))
      (fun m => m + (d : ℤ) ∈ Icc (-(R : ℤ)) (R + 1)) (edgeRetentionMass α r)
    simp only [lost, edgeRetentionTotal]; linarith
  have hlim : Tendsto (fun R : ℕ => lost R / edgeRetentionTotal α r R) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((tendsto_const_nhds (x := (d : ℝ))).div_atTop htot) ?_ ?_
    · filter_upwards [hpos] with R hR using div_nonneg (hlost0 R) hR.le
    · filter_upwards [hpos, hlostd] with R hR hd using div_le_div_of_nonneg_right hd hR.le
  have : Tendsto (fun R : ℕ => 1 - lost R / edgeRetentionTotal α r R) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hlim
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [hpos] with R hR
  rw [hsplit R, sub_div, div_self hR.ne']

/-- With a fixed position cutoff `|n| ≤ Λ` on the translated site, the retained share of the
edge mass tends to zero as the level grows. -/
theorem edgeRetention_cutoff {α r : ℝ} (hr : Real.exp α < r) (d Λ : ℕ) :
    Tendsto (fun R : ℕ =>
      (∑ m ∈ (Icc (-(R : ℤ)) (R + 1)).filter (fun m => m + (d : ℤ) ∈ Icc (-(Λ : ℤ)) Λ),
        edgeRetentionMass α r m) / edgeRetentionTotal α r R) atTop (𝓝 0) := by
  have hr0 : 0 < r := lt_trans (Real.exp_pos α) hr
  have htot := edgeRetentionTotal_tendsto hr
  have hpos : ∀ᶠ R : ℕ in atTop, 0 < edgeRetentionTotal α r R := htot.eventually_gt_atTop 0
  set K : ℝ := ∑ m ∈ Icc (-(Λ : ℤ) - (d : ℤ)) ((Λ : ℤ) - (d : ℤ)), edgeRetentionMass α r m with hK
  have hbound : ∀ R : ℕ,
      (∑ m ∈ (Icc (-(R : ℤ)) (R + 1)).filter (fun m => m + (d : ℤ) ∈ Icc (-(Λ : ℤ)) Λ),
        edgeRetentionMass α r m) ≤ K := by
    intro R
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => (edgeRetentionMass_pos hr0 m).le)
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    omega
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendsto_const_nhds (x := K)).div_atTop htot) ?_ ?_
  · filter_upwards [hpos] with R hR
    exact div_nonneg (Finset.sum_nonneg (fun m _ => (edgeRetentionMass_pos hr0 m).le)) hR.le
  · filter_upwards [hpos] with R hR using div_le_div_of_nonneg_right (hbound R) hR.le


/-- `edgeRetention_uncut` for an integer lag. -/
theorem edgeRetention_uncut_int {α r : ℝ} (hα : 0 ≤ α) (hr : Real.exp α < r) {d : ℤ} (hd : 0 ≤ d) :
    Tendsto (fun R : ℕ =>
      (∑ m ∈ (Icc (-(R : ℤ)) (R + 1)).filter (fun m => m + d ∈ Icc (-(R : ℤ)) (R + 1)),
        edgeRetentionMass α r m) / edgeRetentionTotal α r R) atTop (𝓝 1) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd
  exact edgeRetention_uncut hα hr k

/-- `edgeRetention_cutoff` for an integer lag. -/
theorem edgeRetention_cutoff_int {α r : ℝ} (hr : Real.exp α < r) {d : ℤ} (hd : 0 ≤ d) (Λ : ℕ) :
    Tendsto (fun R : ℕ =>
      (∑ m ∈ (Icc (-(R : ℤ)) (R + 1)).filter (fun m => m + d ∈ Icc (-(Λ : ℤ)) Λ),
        edgeRetentionMass α r m) / edgeRetentionTotal α r R) atTop (𝓝 0) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd
  exact edgeRetention_cutoff hr k Λ

open scoped ComplexConjugate

/-- The weighted pairing of the edge vector with its translate by one lag `d`, with the first
index in `W` and the second in `S`, is `c ^ (-d)` times the edge mass of the sites of `W` whose
translate lies in `S`. -/
theorem edgeRetention_lag_identity (α : ℝ) {c : ℂ} (hc : c ≠ 0) (d : ℤ) (W S : Finset ℤ) :
    ∑ m ∈ W, ∑ n ∈ S, (if n - m = d then
        c ^ (-n) * (conj c) ^ (-m) / (Real.exp (2 * α * |(m : ℝ)|) : ℂ) else 0) =
      c ^ (-d) * ∑ m ∈ W.filter (fun m => m + d ∈ S), (edgeRetentionMass α ‖c‖ m : ℂ) := by
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h1 : ∀ n : ℤ, (n - m = d) ↔ (n = m + d) := fun n => by constructor <;> intro h <;> omega
  simp only [h1]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · have hcc : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have e1 : c ^ (-(m + d)) = c ^ (-d) * c ^ (-m) := by
      rw [← zpow_add₀ hc]; congr 1; ring
    have e2 : c ^ (-m) * (conj c) ^ (-m) = ((‖c‖ ^ (-2 * m) : ℝ) : ℂ) := by
      rw [← mul_zpow, hcc]
      push_cast
      rw [← zpow_natCast, ← zpow_mul]; congr 1; ring
    have e3 : ((Real.exp (-2 * α * |(m : ℝ)|) : ℝ) : ℂ) =
        ((Real.exp (2 * α * |(m : ℝ)|) : ℝ) : ℂ)⁻¹ := by
      rw [show -2 * α * |(m : ℝ)| = -(2 * α * |(m : ℝ)|) by ring, Real.exp_neg]; push_cast; rfl
    unfold edgeRetentionMass
    rw [Complex.ofReal_mul, e3, ← e2, e1]
    ring
  · rfl

/-- Model for the comparison of limits behind Theorem 12.5.1.1, pp. 519–520 (ERRATA M25); not a
statement of the paper. For the zero `c` outside the window, the compression to the edge vector of
the convolution by `φ`, supported on the lags `1, …, D`:
with no position cutoff it tends to the full term `∑ φ d * c ^ (-d)` of that zero;
with any fixed position cutoff `|n| ≤ Λ` it tends to `0`. -/
theorem edgeRetention_compression_limits {α : ℝ} (hα : 0 ≤ α) {c : ℂ}
    (hc : Real.exp α < ‖c‖) (φ : ℤ → ℂ) (D : ℕ)
    (hφ : ∀ k : ℤ, φ k ≠ 0 → k ∈ Icc (1 : ℤ) D) :
    Tendsto (fun R : ℕ =>
        (∑ m ∈ Icc (-(R : ℤ)) (R + 1), ∑ n ∈ Icc (-(R : ℤ)) (R + 1),
          φ (n - m) * (c ^ (-n) * (conj c) ^ (-m) / (Real.exp (2 * α * |(m : ℝ)|) : ℂ))) /
        (edgeRetentionTotal α ‖c‖ R : ℂ))
      atTop (𝓝 (∑ d ∈ Icc (1 : ℤ) D, φ d * c ^ (-d))) ∧
    ∀ Λ : ℕ, Tendsto (fun R : ℕ =>
        (∑ m ∈ Icc (-(R : ℤ)) (R + 1), ∑ n ∈ Icc (-(Λ : ℤ)) Λ,
          φ (n - m) * (c ^ (-n) * (conj c) ^ (-m) / (Real.exp (2 * α * |(m : ℝ)|) : ℂ))) /
        (edgeRetentionTotal α ‖c‖ R : ℂ))
      atTop (𝓝 0) := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact absurd hc (not_lt.mpr (Real.exp_pos α).le)
  -- rewrite the double sum lag by lag
  have key : ∀ (W S : Finset ℤ),
      (∑ m ∈ W, ∑ n ∈ S,
        φ (n - m) * (c ^ (-n) * (conj c) ^ (-m) / (Real.exp (2 * α * |(m : ℝ)|) : ℂ))) =
      ∑ d ∈ Icc (1 : ℤ) D, φ d * (c ^ (-d) *
        ∑ m ∈ W.filter (fun m => m + d ∈ S), (edgeRetentionMass α ‖c‖ m : ℂ)) := by
    intro W S
    have hterm : ∀ m n : ℤ,
        φ (n - m) * (c ^ (-n) * (conj c) ^ (-m) / (Real.exp (2 * α * |(m : ℝ)|) : ℂ)) =
        ∑ d ∈ Icc (1 : ℤ) D, φ d * (if n - m = d then
          c ^ (-n) * (conj c) ^ (-m) / (Real.exp (2 * α * |(m : ℝ)|) : ℂ) else 0) := by
      intro m n
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · have : φ (n - m) = 0 := by
          by_contra h0; exact h (hφ _ h0)
        rw [this, zero_mul]
    simp_rw [hterm]
    calc ∑ m ∈ W, ∑ n ∈ S, ∑ d ∈ Icc (1 : ℤ) D, φ d * (if n - m = d then
            c ^ (-n) * (conj c) ^ (-m) / (Real.exp (2 * α * |(m : ℝ)|) : ℂ) else 0)
        = ∑ d ∈ Icc (1 : ℤ) D, ∑ m ∈ W, ∑ n ∈ S, φ d * (if n - m = d then
            c ^ (-n) * (conj c) ^ (-m) / (Real.exp (2 * α * |(m : ℝ)|) : ℂ) else 0) := by
          rw [Finset.sum_comm (s := Icc (1 : ℤ) D) (t := W)]
          exact Finset.sum_congr rfl (fun m _ => Finset.sum_comm)
      _ = _ := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [← edgeRetention_lag_identity α hc0 d W S, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.mul_sum]
  have hcast : ∀ (R : ℕ) (T : Finset ℤ),
      (∑ m ∈ T, (edgeRetentionMass α ‖c‖ m : ℂ)) / (edgeRetentionTotal α ‖c‖ R : ℂ) =
      (((∑ m ∈ T, edgeRetentionMass α ‖c‖ m) / edgeRetentionTotal α ‖c‖ R : ℝ) : ℂ) := by
    intro R T; push_cast; rfl
  constructor
  · have : Tendsto (fun R : ℕ => ∑ d ∈ Icc (1 : ℤ) D, φ d * (c ^ (-d) *
        (((∑ m ∈ (Icc (-(R : ℤ)) (R + 1)).filter (fun m => m + d ∈ Icc (-(R : ℤ)) (R + 1)),
          edgeRetentionMass α ‖c‖ m) / edgeRetentionTotal α ‖c‖ R : ℝ) : ℂ))) atTop
        (𝓝 (∑ d ∈ Icc (1 : ℤ) D, φ d * (c ^ (-d) * ((1 : ℝ) : ℂ)))) := by
      refine tendsto_finsetSum _ (fun d hd => ?_)
      have hd0 : 0 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
      exact (tendsto_const_nhds.mul
        ((Complex.continuous_ofReal.tendsto _).comp (edgeRetention_uncut_int hα hc hd0))).const_mul _
    simp only [Complex.ofReal_one, mul_one] at this
    refine this.congr (fun R => ?_)
    rw [key, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← hcast]; ring
  · intro Λ
    have : Tendsto (fun R : ℕ => ∑ d ∈ Icc (1 : ℤ) D, φ d * (c ^ (-d) *
        (((∑ m ∈ (Icc (-(R : ℤ)) (R + 1)).filter (fun m => m + d ∈ Icc (-(Λ : ℤ)) Λ),
          edgeRetentionMass α ‖c‖ m) / edgeRetentionTotal α ‖c‖ R : ℝ) : ℂ))) atTop
        (𝓝 (∑ d ∈ Icc (1 : ℤ) D, φ d * (c ^ (-d) * ((0 : ℝ) : ℂ)))) := by
      refine tendsto_finsetSum _ (fun d hd => ?_)
      have hd0 : 0 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
      exact (tendsto_const_nhds.mul
        ((Complex.continuous_ofReal.tendsto _).comp (edgeRetention_cutoff_int hc hd0 Λ))).const_mul _
    simp only [Complex.ofReal_zero, mul_zero, Finset.sum_const_zero] at this
    refine this.congr (fun R => ?_)
    rw [key, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← hcast]; ring

end RiemannMasullo
