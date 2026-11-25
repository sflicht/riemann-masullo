module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Hasse derivatives: the two counting lemmas of Stepanov's method

Stepanov's method bounds the number of points of a curve over `𝔽_Q` by building an auxiliary
polynomial that vanishes to high order at every point to be counted. Its two basic tools on the
affine line are proved here.

* `RiemannMasullo.Polynomial.mul_card_le_natDegree_of_hasseDeriv`: a nonzero polynomial all of
  whose Hasse derivatives of order `< M` vanish at each point of a finite set `S` has degree at
  least `M · #S`.
* `RiemannMasullo.Polynomial.eval_hasseDeriv_mul_pow_expChar`: in exponential characteristic `p`,
  for `Q = p ^ e` and `i < Q`, the `i`-th Hasse derivative of `h · g ^ Q` at `r` is
  `(D⁽ⁱ⁾ h)(r) · g(r) ^ Q`: a `Q`-th power behaves as a constant for derivatives of order `< Q`.
-/

@[expose] public section

namespace RiemannMasullo.Polynomial

open _root_.Polynomial

/-- Stepanov's zero count. A nonzero polynomial over a domain whose Hasse derivatives of order
`< M` all vanish at each point of a finite set `S` has degree at least `M * #S`: each point of `S`
is a root of multiplicity at least `M`. -/
theorem mul_card_le_natDegree_of_hasseDeriv {R : Type*} [CommRing R] [IsDomain R]
    {F : R[X]} (hF : F ≠ 0) (S : Finset R) (M : ℕ)
    (h : ∀ x ∈ S, ∀ i < M, (hasseDeriv i F).eval x = 0) :
    M * S.card ≤ F.natDegree := by
  classical
  have hmult : ∀ x ∈ S, M ≤ F.rootMultiplicity x := by
    intro x hx
    rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
    refine le_natTrailingDegree (mt (taylor_eq_zero x F).mp hF) fun i hi => ?_
    rw [taylor_coeff]
    exact h x hx i hi
  have hle : (∑ x ∈ S, M • ({x} : Multiset R)) ≤ F.roots := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_sum', count_roots]
    by_cases ha : a ∈ S
    · rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb])
          (fun h' => absurd ha h')]
      simpa using hmult a ha
    · rw [Finset.sum_eq_zero fun b hb => by
        have hab : a ≠ b := fun hab => ha (hab ▸ hb)
        simp [hab]]
      exact Nat.zero_le _
  calc M * S.card = Multiset.card (∑ x ∈ S, M • ({x} : Multiset R)) := by
        rw [Multiset.card_sum]
        simp [mul_comm]
    _ ≤ Multiset.card F.roots := Multiset.card_le_card hle
    _ ≤ F.natDegree := card_roots' F

/-- In exponential characteristic `p`, the coefficients of `g ^ (p ^ e)` vanish in every degree
strictly between `0` and `p ^ e`. -/
theorem coeff_pow_expChar_pow_eq_zero {R : Type*} [CommSemiring R] (p : ℕ) [ExpChar R p]
    (e : ℕ) (g : R[X]) {l : ℕ} (hl0 : 0 < l) (hl : l < p ^ e) : (g ^ p ^ e).coeff l = 0 := by
  rw [← map_iterateFrobenius_expand, coeff_map,
    coeff_expand (pow_pos (expChar_pos R p) e)]
  simp [Nat.not_dvd_of_pos_of_lt hl0 hl]

/-- Stepanov's derivative rule. In exponential characteristic `p`, with `Q = p ^ e` and `i < Q`,
the `i`-th Hasse derivative of `h * g ^ Q` at `r` equals `(D⁽ⁱ⁾ h)(r) * g(r) ^ Q`. -/
theorem eval_hasseDeriv_mul_pow_expChar {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]
    (e : ℕ) (h g : R[X]) (r : R) {i : ℕ} (hi : i < p ^ e) :
    (hasseDeriv i (h * g ^ p ^ e)).eval r = (hasseDeriv i h).eval r * g.eval r ^ p ^ e := by
  rw [← taylor_coeff, taylor_apply, mul_comp, pow_comp, ← taylor_apply, ← taylor_apply,
    coeff_mul, Finset.sum_eq_single (i, 0)]
  · rw [taylor_coeff, coeff_zero_eq_eval_zero, eval_pow, taylor_eval, zero_add]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    have hb : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · exact absurd (by simp at hab; simp [hab]) hne
      · exact hb
    rw [coeff_pow_expChar_pow_eq_zero p e _ hb (by omega), mul_zero]
  · intro hn
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) hn

end RiemannMasullo.Polynomial
