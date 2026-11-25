module

public import RiemannMasullo.ForMathlib.NumberTheory.WeilBound.Bombieri
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Weil's bound, IV: plane curves

Let `k` be a finite field with `q` elements and `F ∈ k[t][Y]` monic in `Y` of degree `d ≥ 1`,
separable over `k(t)` (a Bézout relation `U F + V ∂F/∂Y = r(t)` with `r ≠ 0`) and absolutely
irreducible (`L[t][Y]/F` is a domain for an algebraically closed `L ⊇ k`). Then the number `N_n`
of points of the affine curve `F = 0` with coordinates in `𝔽_{q^n} ⊆ L` satisfies
`|N_n - q ^ n| ≤ C q ^ ⌈n/2⌉` for all large `n` (`weil_planeCurve_aux`).

The proof is Bombieri's, with three changes that keep it elementary:
the weighted-degree filtration replaces Riemann–Roch, an expansion at a point over `L` replaces
a rational point, and the lower bound comes from the upper bound for the moved points
(`card_moved_le`) and the count of all points with `t ∈ 𝔽_Q` (`exists_finset_t_fixed`),
instead of from a Galois closure.
-/

@[expose] public section

open Polynomial

namespace RiemannMasullo.WeilBound

/-- The arithmetic of Bombieri's parameters. With `K = e (e + c₁) + 1`, `M = c₁ + K - 1`,
`a = (q₁ - c₁ - 1) / d` and `b = (e q₀ + M) / d`, as soon as `q₀ ≤ q₁` and
`q₁ > 2 c₁ K + e (M + d N + d)`: the non-cancellation condition `d a + c₁ < q₁` holds, the
linear system has more unknowns than equations, and the resulting count is
`≤ e q₀ q₁ + (M + 1) q₁ + c₁`. -/
theorem bombieri_params (d c₁ e N q₀ q₁ : ℕ) (hd : 0 < d) (hq : q₀ ≤ q₁)
    (hT : 2 * c₁ * (e * (e + c₁) + 1) + e * (c₁ + e * (e + c₁) + d * N + d) < q₁) :
    d * ((q₁ - c₁ - 1) / d) + c₁ < q₁ ∧
    (∀ cb fa : ℕ, d * ((e * q₀ + (c₁ + e * (e + c₁))) / d + 1) ≤ cb + c₁ →
      d * ((q₁ - c₁ - 1) / d + 1) ≤ fa + c₁ →
      e * (d * (q₀ * ((q₁ - c₁ - 1) / d) + (e * q₀ + (c₁ + e * (e + c₁))) / d + N + 1)) <
        cb * fa) ∧
    d * ((q₁ - c₁ - 1) / d + q₁ * ((e * q₀ + (c₁ + e * (e + c₁))) / d)) + c₁ ≤
      e * (q₀ * q₁) + (c₁ + e * (e + c₁) + 1) * q₁ + c₁ := by
  set K := e * (e + c₁) + 1 with hK
  set M := c₁ + e * (e + c₁) with hM
  set a := (q₁ - c₁ - 1) / d with ha
  set b := (e * q₀ + M) / d with hb
  have hc₁ : 2 * c₁ < q₁ := by
    have : 2 * c₁ ≤ 2 * c₁ * K := Nat.le_mul_of_pos_right _ (by omega)
    omega
  -- division facts
  have ha1 : d * a ≤ q₁ - c₁ - 1 := Nat.mul_div_le _ _
  have ha2 : q₁ - c₁ - 1 < d * (a + 1) := by
    rw [mul_add, mul_one]; exact Nat.lt_mul_div_succ _ hd
  have hb1 : d * b ≤ e * q₀ + M := Nat.mul_div_le _ _
  have hb2 : e * q₀ + M < d * (b + 1) := by
    rw [mul_add, mul_one]; exact Nat.lt_mul_div_succ _ hd
  refine ⟨by omega, ?_, ?_⟩
  · intro cb fa hcb hfa
    -- work in ℤ
    have hcb' : (e * q₀ + K : ℤ) ≤ cb := by push_cast [hM] at hb2 ⊢; omega
    have hfa' : ((q₁ : ℤ) - 2 * c₁) ≤ fa := by omega
    have hfa0 : (0 : ℤ) ≤ (q₁ : ℤ) - 2 * c₁ := by omega
    have hprod : ((e * q₀ + K : ℤ)) * ((q₁ : ℤ) - 2 * c₁) ≤ (cb : ℤ) * fa :=
      mul_le_mul hcb' hfa' hfa0 (by positivity)
    have hlhs : (e : ℤ) * (d * (q₀ * a + b + N + 1)) ≤
        e * (q₀ * ((q₁ : ℤ) - c₁ - 1) + (e * q₀ + M) + d * (N + 1)) := by
      have h1 : (d : ℤ) * a ≤ q₁ - c₁ - 1 := by omega
      have h2 : (d : ℤ) * b ≤ e * q₀ + M := by exact_mod_cast hb1
      have h3 : (d : ℤ) * (q₀ * a + b + N + 1) =
          q₀ * (d * a) + d * b + d * (N + 1) := by ring
      rw [h3]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : (q₀ : ℤ) * (d * a) ≤ q₀ * (q₁ - c₁ - 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    have hkey : (e : ℤ) * (q₀ * ((q₁ : ℤ) - c₁ - 1) + (e * q₀ + M) + d * (N + 1)) <
        (e * q₀ + K : ℤ) * ((q₁ : ℤ) - 2 * c₁) := by
      have hT' : (2 * c₁ * K + e * (M + d * N + d) : ℤ) < q₁ := by
        push_cast [hK, hM] at hT ⊢; linarith
      have hq' : (q₀ : ℤ) ≤ q₁ := by exact_mod_cast hq
      have hK' : (K : ℤ) = e * (e + c₁) + 1 := by push_cast [hK]; ring
      have hM' : (M : ℤ) = c₁ + e * (e + c₁) := by push_cast [hM]; ring
      have he0 : (0 : ℤ) ≤ e := by positivity
      have hc0 : (0 : ℤ) ≤ c₁ := by positivity
      have hq0 : (0 : ℤ) ≤ q₀ := by positivity
      have hmono : (e : ℤ) * (c₁ + e - 1) * q₀ ≤ (K - 1) * q₁ := by
        rw [hK']
        have : (e : ℤ) * (c₁ + e - 1) ≤ e * (e + c₁) := by nlinarith
        have h0 : (0 : ℤ) ≤ e * (e + c₁) := by positivity
        calc (e : ℤ) * (c₁ + e - 1) * q₀ ≤ e * (e + c₁) * q₀ :=
              mul_le_mul_of_nonneg_right this hq0
          _ ≤ e * (e + c₁) * q₁ := mul_le_mul_of_nonneg_left hq' h0
          _ = _ := by ring
      nlinarith
    have := hlhs.trans_lt (hkey.trans_le hprod)
    exact_mod_cast this
  · have h1 : d * (q₁ * b) ≤ q₁ * (e * q₀ + M) := by
      rw [mul_left_comm]; exact Nat.mul_le_mul_left _ hb1
    have h2 : q₁ * (e * q₀ + M) = e * (q₀ * q₁) + M * q₁ := by ring
    rw [mul_add]
    have : (M + 1) * q₁ = M * q₁ + q₁ := by ring
    omega


section Total

variable {k : Type*} [Field k] [Fintype k] {F : k[X][X]} (hF : F.Monic)

/-- The point of `A = k[t][Y]/F` over the point `t = c`, `y = η` of the plane curve. -/
noncomputable def pointOf {L : Type*} [Field L] [Algebra k L] (c η : L)
    (h : (F.map (aeval c).toRingHom).eval η = 0) : AdjoinRoot F →ₐ[k] L :=
  AdjoinRoot.liftAlgHom F (aeval c) η (by rw [← eval_map]; exact h)

theorem pointOf_of {L : Type*} [Field L] [Algebra k L] (c η : L) (h) :
    pointOf (F := F) c η h (AdjoinRoot.of F X) = c := by
  simp [pointOf]

theorem pointOf_root {L : Type*} [Field L] [Algebra k L] (c η : L) (h) :
    pointOf (F := F) c η h (AdjoinRoot.root F) = η := by
  simp [pointOf]

include hF in
/-- **The total count.** Over an algebraically closed `L`, if `F` is separable over `k(t)`
(Bézout relation `U F + V F' = r(t)`, `r ≠ 0`), then at least `d (Q - deg r)` points of the curve
have `t ∈ 𝔽_Q`: each `c ∈ 𝔽_Q` with `r (c) ≠ 0` carries `d` distinct points. -/
theorem exists_finset_t_fixed (L : Type*) [Field L] [IsAlgClosed L] [Algebra k L]
    {U V : k[X][X]} {r : k[X]} (hr : r ≠ 0) (hUV : U * F + V * derivative F = C r)
    (n : ℕ) (hn : 0 < n) :
    ∃ s : Finset (AdjoinRoot F →ₐ[k] L),
      (∀ φ ∈ s, φ (AdjoinRoot.of F X) ^ (Fintype.card k ^ n) = φ (AdjoinRoot.of F X)) ∧
      F.natDegree * (Fintype.card k ^ n - r.natDegree) ≤ s.card := by
  classical
  set q := Fintype.card k
  obtain ⟨p, hchar⟩ := CharP.exists k
  have hp : p.Prime := CharP.char_is_prime k p
  have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  have hq : 1 < q ^ n := Nat.one_lt_pow hn.ne' Fintype.one_lt_card
  -- the `Q` elements of `𝔽_Q ⊆ L`
  set G : L[X] := X ^ (q ^ n) - X
  have hpq : p ∣ q ^ n := by
    obtain ⟨m, hm, hcard⟩ := FiniteField.card k p
    rw [show q = Fintype.card k from rfl, hcard, ← pow_mul]
    exact dvd_pow_self p (Nat.mul_ne_zero m.pos.ne' hn.ne')
  have hGsep : G.Separable := galois_poly_separable p (q ^ n) hpq
  have hGdeg : G.natDegree = q ^ n := natDegree_X_pow_sub_X hq
  set R := G.roots.toFinset
  have hRcard : R.card = q ^ n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hGsep), IsAlgClosed.card_roots_eq_natDegree,
      hGdeg]
  have hR : ∀ c ∈ R, c ^ (q ^ n) = c := by
    intro c hc
    have hG0 : G ≠ 0 := by intro h; rw [h, natDegree_zero] at hGdeg; omega
    rw [Multiset.mem_toFinset, mem_roots hG0, IsRoot.def] at hc
    simpa [G, sub_eq_zero] using hc
  -- the good `c`
  set R' := R.filter (fun c => aeval c r ≠ 0)
  have hR'card : q ^ n - r.natDegree ≤ R'.card := by
    have hbad : (R.filter (fun c => aeval c r = 0)).card ≤ r.natDegree := by
      have hrm : r.map (algebraMap k L) ≠ 0 := (Polynomial.map_ne_zero hr)
      calc (R.filter (fun c => aeval c r = 0)).card
          ≤ (r.map (algebraMap k L)).roots.toFinset.card := by
            apply Finset.card_le_card
            intro c hc
            rw [Finset.mem_filter] at hc
            rw [Multiset.mem_toFinset, mem_roots hrm, IsRoot.def, eval_map, ← aeval_def]
            exact hc.2
        _ ≤ (r.map (algebraMap k L)).roots.card := Multiset.toFinset_card_le _
        _ ≤ (r.map (algebraMap k L)).natDegree := card_roots' _
        _ ≤ r.natDegree := natDegree_map_le
    have := Finset.card_filter_add_card_filter_not (s := R) (fun c => aeval c r = 0)
    have e : R'.card = (R.filter fun a => ¬ aeval a r = 0).card := rfl
    omega
  -- the fibre over a good `c`
  have hfib : ∀ c ∈ R', ((F.map (aeval c).toRingHom).roots.toFinset).card = F.natDegree := by
    intro c hc
    have hrc : aeval c r ≠ 0 := (Finset.mem_filter.1 hc).2
    set Fc := F.map (aeval c).toRingHom
    have hsep : Fc.Separable := by
      refine ⟨C (aeval c r)⁻¹ * U.map (aeval c).toRingHom,
        C (aeval c r)⁻¹ * V.map (aeval c).toRingHom, ?_⟩
      have h1 := congrArg (Polynomial.map (aeval c).toRingHom) hUV
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
        ← derivative_map] at h1
      rw [mul_assoc, mul_assoc, ← mul_add, h1, ← C_mul]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [inv_mul_cancel₀ hrc, C_1]
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
      hF.natDegree_map]
  -- assemble
  let pt : (Σ c : R', ((F.map (aeval (c : L)).toRingHom).roots.toFinset)) →
      (AdjoinRoot F →ₐ[k] L) := fun x =>
    pointOf (x.1 : L) (x.2 : L) (by
      have hx := x.2.2
      rw [Multiset.mem_toFinset] at hx
      have h0 : F.map (aeval (x.1 : L)).toRingHom ≠ 0 := (hF.map _).ne_zero
      exact (mem_roots h0).1 hx)
  have hpt : Function.Injective pt := by
    rintro ⟨c, η⟩ ⟨c', η'⟩ h
    have h1 : (c : L) = c' := by
      have := congrArg (fun φ => φ (AdjoinRoot.of F X)) h
      simpa [pt, pointOf] using this
    have h2 : (η : L) = η' := by
      have := congrArg (fun φ => φ (AdjoinRoot.root F)) h
      simpa [pt, pointOf] using this
    have hc : c = c' := Subtype.ext h1
    subst hc
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Subtype.ext h2
  refine ⟨Finset.univ.image pt, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hφ
    have : pt x (AdjoinRoot.of F X) = x.1 := by simp [pt, pointOf]
    rw [this]
    exact hR _ (Finset.mem_filter.1 x.1.2).1
  · rw [Finset.card_image_of_injective _ hpt, Finset.card_univ, Fintype.card_sigma]
    have : ∑ c : R', Fintype.card ((F.map (aeval (c : L)).toRingHom).roots.toFinset) =
        ∑ _c : R', F.natDegree := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Fintype.card_coe, hfib c c.2]
    rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_comm]
    exact Nat.mul_le_mul_right _ hR'card

end Total


section Main

variable {k : Type*} [Field k] [Fintype k] {F : k[X][X]}

theorem exists_weight (F : k[X][X]) :
    ∃ w, ∀ i < F.natDegree, (F.coeff i).natDegree ≤ (F.natDegree - i) * w := by
  refine ⟨∑ j ∈ Finset.range F.natDegree, (F.coeff j).natDegree, fun i hi => ?_⟩
  have h1 : (F.coeff i).natDegree ≤ ∑ j ∈ Finset.range F.natDegree, (F.coeff j).natDegree :=
    Finset.single_le_sum (f := fun j => (F.coeff j).natDegree) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hi)
  exact h1.trans (Nat.le_mul_of_pos_left _ (by omega))

theorem exists_quot_bound (hF : F.Monic) (w : ℕ) :
    ∃ N₀, ∀ i, (quot F).coeff i ∈ filt hF w N₀ := by
  classical
  choose deg hdeg using fun i => exists_mem_filt hF w ((quot F).coeff i)
  refine ⟨∑ i ∈ Finset.range ((quot F).natDegree + 1), deg i, fun i => ?_⟩
  by_cases hi : i ≤ (quot F).natDegree
  · exact filt_mono hF w (Finset.single_le_sum (f := deg) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) (hdeg i)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Submodule.zero_mem _


/-- An expansion point: since `L` is algebraically closed and `F` is separable over `k(t)`, the
curve has a point `(c, η)` over `L` where `∂F/∂Y ≠ 0`, and so an expansion there. -/
theorem exists_expansion (hF : F.Monic) (hd : 0 < F.natDegree) (L : Type*) [Field L]
    [IsAlgClosed L] [Algebra k L] {U V : k[X][X]} {r : k[X]} (hr : r ≠ 0)
    (hUV : U * F + V * derivative F = C r) :
    ∃ (ψ : AdjoinRoot (baseChange L F) →ₐ[L] PowerSeries L) (c : L),
      ψ (AdjoinRoot.of _ X) = PowerSeries.C c + PowerSeries.X := by
  classical
  have hrm : r.map (algebraMap k L) ≠ 0 := Polynomial.map_ne_zero hr
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (r.map (algebraMap k L)).roots.toFinset
  have hrc : aeval c r ≠ 0 := by
    intro h
    apply hc
    rw [Multiset.mem_toFinset, mem_roots hrm, IsRoot.def, eval_map, ← aeval_def]
    exact h
  set Fc := F.map (aeval c).toRingHom
  have hFc : (baseChange L F).map (evalRingHom c) = Fc := by
    rw [baseChange, Polynomial.map_map]
    congr 1
    apply Polynomial.ringHom_ext <;> simp
  have hdeg : Fc.degree ≠ 0 := by
    rw [degree_eq_natDegree (hF.map _).ne_zero, hF.natDegree_map]
    exact_mod_cast hd.ne'
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_root Fc hdeg
  have h1 := congrArg (fun p => (p.map (aeval c).toRingHom).eval η) hUV
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, eval_add, eval_mul,
    eval_C, ← derivative_map] at h1
  rw [show eval η (F.map (aeval c).toRingHom) = 0 from hη, mul_zero, zero_add] at h1
  have hder : Fc.derivative.eval η ≠ 0 := by
    intro h0
    have h0' : eval η (derivative (map (aeval c).toRingHom F)) = 0 := h0
    rw [h0', mul_zero] at h1
    exact hrc (by simpa using h1.symm)
  obtain ⟨ψ, hψ⟩ := exists_algHom_powerSeries (baseChange_monic L hF) c η
    (by rw [hFc]; exact hη) (by rw [hFc]; exact hder)
  exact ⟨ψ, c, hψ⟩


theorem weil_final_arith {n₁ n₂ d Q q₁ K₁ K₂ c₁ D : ℤ} (_hd : 1 ≤ d) (hq : 1 ≤ q₁)
    (hc : 0 ≤ c₁) (hD : 0 ≤ D) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (e1 : n₁ ≤ Q + K₁ * q₁ + c₁) (e2 : n₂ ≤ (d - 1) * Q + K₂ * q₁ + c₁)
    (e3 : d * Q - D ≤ n₁ + n₂) :
    |n₁ - Q| ≤ (K₁ + K₂ + c₁ + c₁ + D) * q₁ := by
  have h1 : c₁ ≤ c₁ * q₁ := by nlinarith
  have h2 : D ≤ D * q₁ := by nlinarith
  have h3 : 0 ≤ K₂ * q₁ := by positivity
  have h4 : 0 ≤ K₁ * q₁ := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-- **Weil's bound for plane curves, explicit form.** For `n ≥ n₀`, with `Q = q ^ n`,
`q₁ = q ^ (n - n / 2)`, the number `N` of points of `F = 0` over `𝔽_Q` (in `L`) satisfies
`|N - Q| ≤ C q₁`. -/
theorem weil_planeCurve_aux (hF : F.Monic) (hd : 0 < F.natDegree) (L : Type*) [Field L]
    [IsAlgClosed L] [Algebra k L] {U V : k[X][X]} {r : k[X]} (hr : r ≠ 0)
    (hUV : U * F + V * derivative F = C r) [IsDomain (AdjoinRoot (baseChange L F))] :
    ∃ C n₀ : ℕ, ∀ n ≥ n₀,
      {φ : AdjoinRoot F →ₐ[k] L |
        φ (AdjoinRoot.of F X) ^ (Fintype.card k ^ n) = φ (AdjoinRoot.of F X) ∧
        φ (AdjoinRoot.root F) ^ (Fintype.card k ^ n) = φ (AdjoinRoot.root F)}.Finite ∧
      |({φ : AdjoinRoot F →ₐ[k] L |
        φ (AdjoinRoot.of F X) ^ (Fintype.card k ^ n) = φ (AdjoinRoot.of F X) ∧
        φ (AdjoinRoot.root F) ^ (Fintype.card k ^ n) = φ (AdjoinRoot.root F)}.ncard : ℤ) -
          Fintype.card k ^ n| ≤ C * Fintype.card k ^ (n - n / 2) := by
  classical
  set q := Fintype.card k with hq_def
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  set d := F.natDegree with hd_def
  obtain ⟨w, hw⟩ := exists_weight F
  set c₁ := w * d * d
  obtain ⟨ψ, c, hψ⟩ := exists_expansion hF hd L hr hUV
  obtain ⟨N₀, hN₀⟩ := exists_quot_bound hF w
  -- thresholds
  obtain ⟨T₁, hT₁⟩ : ∃ T₁, T₁ = 2 * c₁ * (1 * (1 + c₁) + 1) + 1 * (c₁ + 1 * (1 + c₁) + d * 0 + d) :=
    ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ T₂, T₂ = 2 * c₁ * ((d - 1) * ((d - 1) + c₁) + 1) +
    (d - 1) * (c₁ + (d - 1) * ((d - 1) + c₁) + d * N₀ + d) := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, K₁ = c₁ + 1 * (1 + c₁) + 1 := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂, K₂ = c₁ + (d - 1) * ((d - 1) + c₁) + 1 := ⟨_, rfl⟩
  refine ⟨K₁ + K₂ + c₁ + c₁ + d * r.natDegree, 2 * (T₁ + T₂ + 1), fun n hn => ?_⟩
  set m₀ := n / 2
  set m₁ := n - n / 2
  have hm : m₀ + m₁ = n := by omega
  set q₀ := q ^ m₀
  set q₁ := q ^ m₁
  have hq01 : q₀ ≤ q₁ := Nat.pow_le_pow_right (by omega) (by omega)
  have hq1 : T₁ + T₂ < q₁ := by
    calc T₁ + T₂ < m₁ := by omega
      _ < 2 ^ m₁ := Nat.lt_two_pow_self
      _ ≤ q₁ := Nat.pow_le_pow_left hq2 _
  have hq1a : T₁ < q₁ := by omega
  have hq1b : T₂ < q₁ := by omega
  have hQ : q ^ n = q₀ * q₁ := by rw [← pow_add, hm]
  -- the fixed points
  obtain ⟨hA1, hB1, hC1⟩ := bombieri_params d c₁ 1 0 q₀ q₁ hd hq01 (hT₁ ▸ hq1a)
  have hfix := card_fixed_le hF hw ψ c hψ (m₀ := m₀) (m₁ := m₁)
    (a := (q₁ - c₁ - 1) / d) (b := (1 * q₀ + (c₁ + 1 * (1 + c₁))) / d) hA1 (by
    have := hB1 _ _ (le_card_idx w _) (le_finrank_filt hF w _)
    rw [one_mul, add_zero] at this
    exact this) L
  rw [hm] at hfix
  -- the moved points
  obtain ⟨hA2, hB2, hC2⟩ := bombieri_params d c₁ (d - 1) N₀ q₀ q₁ hd hq01 (hT₂ ▸ hq1b)
  have hmov := card_moved_le hF hw ψ c hψ hd hN₀ (m₀ := m₀) (m₁ := m₁)
    (a := (q₁ - c₁ - 1) / d) (b := ((d - 1) * q₀ + (c₁ + (d - 1) * ((d - 1) + c₁))) / d) hA2 (by
    have := hB2 _ _ (le_card_idx w _) (le_finrank_filt hF w _)
    exact this) L
  rw [hm] at hmov
  -- the total
  obtain ⟨s, hs, hscard⟩ := exists_finset_t_fixed hF L hr hUV n (by omega)
  set S₁ := {φ : AdjoinRoot F →ₐ[k] L |
        φ (AdjoinRoot.of F X) ^ (q ^ n) = φ (AdjoinRoot.of F X) ∧
        φ (AdjoinRoot.root F) ^ (q ^ n) = φ (AdjoinRoot.root F)}
  set S₂ := {φ : AdjoinRoot F →ₐ[k] L |
        φ (AdjoinRoot.of F X) ^ (q ^ n) = φ (AdjoinRoot.of F X) ∧
        φ (AdjoinRoot.root F) ^ (q ^ n) ≠ φ (AdjoinRoot.root F)}
  have hsub : (s : Set (AdjoinRoot F →ₐ[k] L)) ⊆ S₁ ∪ S₂ := by
    intro φ hφ
    by_cases h : φ (AdjoinRoot.root F) ^ (q ^ n) = φ (AdjoinRoot.root F)
    · exact Or.inl ⟨hs φ hφ, h⟩
    · exact Or.inr ⟨hs φ hφ, h⟩
  have hdisj : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    intro φ h1 h2
    exact h2.2 h1.2
  have htot : s.card ≤ S₁.ncard + S₂.ncard := by
    rw [← Set.ncard_union_eq hdisj hfix.1 hmov.1, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (hfix.1.union hmov.1)
  refine ⟨hfix.1, ?_⟩
  -- arithmetic
  rw [← hK₁] at hC1
  rw [← hK₂] at hC2
  have e1 : (S₁.ncard : ℤ) ≤ 1 * (q₀ * q₁) + K₁ * q₁ + c₁ := by
    exact_mod_cast hfix.2.trans hC1
  have e2 : (S₂.ncard : ℤ) ≤ (d - 1 : ℕ) * (q₀ * q₁) + K₂ * q₁ + c₁ := by
    exact_mod_cast hmov.2.trans hC2
  have e3 : (d : ℤ) * (q ^ n - r.natDegree) ≤ S₁.ncard + S₂.ncard := by
    have h1 : (d : ℤ) * ((q ^ n - r.natDegree : ℕ) : ℤ) ≤ S₁.ncard + S₂.ncard := by
      exact_mod_cast hscard.trans htot
    have h2 : ((q : ℤ) ^ n - r.natDegree) ≤ ((q ^ n - r.natDegree : ℕ) : ℤ) := by
      rcases le_or_gt r.natDegree (q ^ n) with h | h
      · rw [Nat.cast_sub h]; push_cast; exact le_rfl
      · rw [Nat.sub_eq_zero_of_le h.le]
        have : ((q ^ n : ℕ) : ℤ) < r.natDegree := by exact_mod_cast h
        push_cast at this ⊢
        linarith
    have h3 : (0 : ℤ) ≤ d := by positivity
    calc (d : ℤ) * (q ^ n - r.natDegree) ≤ d * ((q ^ n - r.natDegree : ℕ) : ℤ) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ ≤ _ := h1
  have hd1 : ((d - 1 : ℕ) : ℤ) = d - 1 := by push_cast [Nat.cast_sub hd]; ring
  have hQ' : (q : ℤ) ^ n = q₀ * q₁ := by exact_mod_cast hQ
  have hq1pos : (1 : ℤ) ≤ q₁ := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
  rw [hd1] at e2
  rw [hQ'] at e3
  clear_value S₁ S₂
  clear hB1 hB2 hC1 hC2 hfix hmov hsub htot hscard hs
  have key := weil_final_arith (n₁ := S₁.ncard) (n₂ := S₂.ncard) (d := d) (Q := q₀ * q₁)
    (q₁ := q₁) (K₁ := K₁) (K₂ := K₂) (c₁ := c₁) (D := d * r.natDegree)
    (by exact_mod_cast hd) hq1pos (by positivity) (by positivity) (by positivity)
    (by positivity) (by simpa using e1) e2 (by rw [mul_sub] at e3; exact e3)
  have hq₁c : ((q₁ : ℕ) : ℤ) = (q : ℤ) ^ m₁ := by push_cast [q₁]; rfl
  rw [hQ']
  convert key using 1
  push_cast
  rw [hq₁c]

end Main

end RiemannMasullo.WeilBound
