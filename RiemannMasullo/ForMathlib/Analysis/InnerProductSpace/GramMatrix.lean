module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! # Finite Gram matrices and coefficient norms -/

@[expose] public noncomputable section

open Set
open scoped InnerProductSpace

namespace RiemannMasullo

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {u : ι → H}

/-- The sharp coefficient ratio on a finite independent family is the square root
of the matching inverse Gram diagonal entry. The inverse Gram column attains it. -/
theorem finiteGram_coefficient_isGreatest [Fintype ι] [DecidableEq ι]
    (hu : LinearIndependent ℂ u) (i : ι) :
    IsGreatest (range fun c : ι → ℂ ↦ ‖c i‖ / ‖∑ j, c j • u j‖)
      (Real.sqrt ((Matrix.gram ℂ u)⁻¹ i i).re) := by
  let a (j : ι) := (Matrix.gram ℂ u)⁻¹ j i
  let q := ∑ j, a j • u j
  have hdet := isUnit_iff_ne_zero.mpr (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hu)
  have hinner (j : ι) : ⟪q, u j⟫_ℂ = if j = i then 1 else 0 := by
    have h := congrArg (fun M : Matrix ι ι ℂ ↦ M j i) ((Matrix.gram ℂ u).mul_nonsing_inv hdet)
    have hright : ⟪u j, q⟫_ℂ = (1 : Matrix ι ι ℂ) j i := by
      simpa only [q, a, inner_sum, inner_smul_right, Matrix.mul_apply, Matrix.gram_apply, mul_comm]
        using h
    rw [← inner_conj_symm q (u j), hright, Matrix.one_apply]
    split <;> simp
  have hcoeff (c : ι → ℂ) : ⟪q, ∑ j, c j • u j⟫_ℂ = c i := by
    simp [inner_sum, inner_smul_right, hinner, mul_ite]
  have hdiag : ⟪q, q⟫_ℂ = (Matrix.gram ℂ u)⁻¹ i i := hcoeff a
  have hnorm : ((Matrix.gram ℂ u)⁻¹ i i).re = ‖q‖ ^ 2 :=
    hdiag ▸ inner_self_eq_norm_sq (𝕜 := ℂ) q
  rw [hnorm, Real.sqrt_sq (norm_nonneg _)]
  constructor
  · refine ⟨a, ?_⟩
    change ‖(Matrix.gram ℂ u)⁻¹ i i‖ / ‖q‖ = ‖q‖
    rw [← hdiag, ← inner_self_re_eq_norm, inner_self_eq_norm_mul_norm, mul_self_div_self]
  · rintro _ ⟨c, rfl⟩
    rcases eq_or_lt_of_le (norm_nonneg (∑ j, c j • u j)) with h | h
    · simp [← h]
    exact (div_le_iff₀ h).mpr ((hcoeff c) ▸ norm_inner_le_norm (𝕜 := ℂ) q _)

/-- Square root of the `i`th inverse Gram diagonal of the finite block `S`, extended by
zero at indices outside the block. This convention lets every coordinate use the same matrix. -/
def finiteGramCoordinate (u : ι → H) (i : ι) (S : Finset ι) : ℝ := by
  classical
  exact if hi : i ∈ S then
    Real.sqrt ((Matrix.gram ℂ (fun j : S ↦ u j.val))⁻¹ ⟨i, hi⟩ ⟨i, hi⟩).re else 0

/-- The principal Gram value is the attained maximum over all coefficient vectors
supported on the same finite block. -/
theorem finiteGramCoordinate_isGreatest (hu : LinearIndependent ℂ u) (i : ι) (S : Finset ι) :
    IsGreatest ((fun c : ι →₀ ℂ ↦ ‖c i‖ / ‖Finsupp.linearCombination ℂ u c‖) ''
      {c | c.support ⊆ S}) (finiteGramCoordinate u i S) := by
  classical
  by_cases hi : i ∈ S
  · let k : S := ⟨i, hi⟩
    let e : S ↪ ι := Function.Embedding.subtype (· ∈ S)
    let v : S → H := u ∘ e
    have hmax := finiteGram_coefficient_isGreatest (hu.comp e e.injective) k
    have hval : finiteGramCoordinate u i S = Real.sqrt ((Matrix.gram ℂ v)⁻¹ k k).re := by
      simp only [finiteGramCoordinate, hi, dite_eq_left, k, v, e, Function.comp_def,
        Function.Embedding.subtype_apply]
    rw [hval]
    constructor
    · obtain ⟨c, hc⟩ := hmax.1
      let d : S →₀ ℂ := Finsupp.equivFunOnFinite.symm c
      have heval : d.embDomain e i = c k := Finsupp.embDomain_apply_self e d k
      have hsum : Finsupp.linearCombination ℂ u (d.embDomain e) = ∑ j, c j • v j := by
        rw [Finsupp.linearCombination_embDomain, Finsupp.linearCombination_apply]
        exact d.sum_fintype (fun j a ↦ a • v j) (fun _ ↦ zero_smul _ _)
      refine ⟨d.embDomain e, ?_, ?_⟩
      · intro j hj
        rw [Finsupp.support_embDomain, Finset.mem_map] at hj
        obtain ⟨l, _, rfl⟩ := hj
        exact l.property
      · change ‖d.embDomain e i‖ / ‖Finsupp.linearCombination ℂ u (d.embDomain e)‖ = _
        rw [heval, hsum]
        exact hc
    · rintro _ ⟨c, hsupport, rfl⟩
      have hsum : Finsupp.linearCombination ℂ u c = ∑ j : S, c j.val • u j.val := by
        rw [Finset.sum_coe_sort S (fun j : ι ↦ c j • u j)]
        exact Finsupp.linearCombination_apply_of_mem_supported ℂ ((Finsupp.mem_supported ℂ c).2
          (Finset.coe_subset.mpr hsupport))
      change ‖c i‖ / ‖Finsupp.linearCombination ℂ u c‖ ≤ _
      rw [hsum]
      exact hmax.2 (mem_range_self (fun j : S ↦ c j.val))
  · rw [finiteGramCoordinate, dite_eq_right hi]
    constructor
    · exact ⟨0, by simp, by simp⟩
    · rintro _ ⟨c, hsupport, rfl⟩
      have hc : c i = 0 := Finsupp.notMem_support_iff.mp (fun h ↦ hi (hsupport h))
      simp [hc]

/-- For an arbitrary independent family, the coefficient ratios and the square roots of the
principal inverse Gram diagonal entries have the same least upper bounds. -/
theorem finiteGram_coefficient_isLUB_iff (hu : LinearIndependent ℂ u) (i : ι) (b : ℝ) :
    IsLUB (range (fun c : ι →₀ ℂ ↦ ‖c i‖ / ‖Finsupp.linearCombination ℂ u c‖)) b ↔
      IsLUB (range (finiteGramCoordinate u i)) b := by
  have heq : upperBounds (range (fun c : ι →₀ ℂ ↦ ‖c i‖ / ‖Finsupp.linearCombination ℂ u c‖)) =
      upperBounds (range (finiteGramCoordinate u i)) := by
    ext a
    constructor
    · rintro h _ ⟨S, rfl⟩
      obtain ⟨c, _, hc⟩ := (finiteGramCoordinate_isGreatest hu i S).1
      exact h ⟨c, hc⟩
    · rintro h _ ⟨c, rfl⟩
      exact ((finiteGramCoordinate_isGreatest hu i c.support).2 ⟨c, Finset.Subset.rfl, rfl⟩).trans
        (h (mem_range_self c.support))
  change IsLeast _ b ↔ IsLeast _ b
  rw [heq]

private theorem finiteGram_inv_diag_smul [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (ha : ∀ j, a j ≠ 0) (i : ι) :
    ((Matrix.gram ℂ (fun j ↦ a j • u j))⁻¹ i i).re =
      (‖a i‖⁻¹)^2 * ((Matrix.gram ℂ u)⁻¹ i i).re := by
  have hinv (d : ι → ℂ) (hd : ∀ j, d j ≠ 0) :
      (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun j ↦ (d j)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    simp [Matrix.diagonal_mul_diagonal, hd]
  have hg : Matrix.gram ℂ (fun j ↦ a j • u j) =
      Matrix.diagonal (fun j ↦ star (a j)) * Matrix.gram ℂ u * Matrix.diagonal a := by
    ext j k
    simp only [Matrix.gram_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, inner_smul_left,
      inner_smul_right, starRingEnd_apply]
    ring
  have hd : ((Matrix.gram ℂ (fun j ↦ a j • u j))⁻¹ i i) =
      ((a i)⁻¹ * (star (a i))⁻¹) * ((Matrix.gram ℂ u)⁻¹ i i) := by
    rw [hg, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hinv a ha,
      hinv (fun j ↦ star (a j)) (fun j ↦ star_ne_zero.mpr (ha j)), Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hp : (a i)⁻¹ * (star (a i))⁻¹ = (((‖a i‖⁻¹)^2 : ℝ) : ℂ) := by
    rw [← star_inv₀]
    simpa only [starRingEnd_apply, norm_inv, Complex.ofReal_pow] using Complex.mul_conj' ((a i)⁻¹)
  rw [hd, hp, Complex.re_ofReal_mul]

/-- Each principal inverse Gram coordinate scales by the reciprocal modulus at the
selected index. Only scalars on the finite block need to be nonzero. -/
theorem finiteGramCoordinate_smul (a : ι → ℂ) (i : ι) (S : Finset ι)
    (ha : ∀ j ∈ S, a j ≠ 0) :
    finiteGramCoordinate (fun j ↦ a j • u j) i S = ‖a i‖⁻¹ * finiteGramCoordinate u i S := by
  classical
  by_cases hi : i ∈ S
  · simp only [finiteGramCoordinate, hi, dite_eq_left]
    rw [finiteGram_inv_diag_smul (u := fun j : S ↦ u j.val) (fun j ↦ a j.val) (fun j ↦ ha _ j.property),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr (norm_nonneg _))]
  · simp [finiteGramCoordinate, hi]

/-- The condition number is unchanged by independent rescalings of the vectors. -/
theorem norm_mul_finiteGramCoordinate_smul (a : ι → ℂ) (i : ι) (S : Finset ι)
    (ha : ∀ j ∈ S, a j ≠ 0) :
    ‖a i • u i‖ * finiteGramCoordinate (fun j ↦ a j • u j) i S = ‖u i‖ * finiteGramCoordinate u i S := by
  by_cases hi : i ∈ S
  · rw [finiteGramCoordinate_smul a i S ha, norm_smul]
    field_simp [norm_ne_zero_iff.mpr (ha i hi)]
  · simp [finiteGramCoordinate, hi]

open Classical in
/-- On a finite block the condition number is the square root of the inverse Gram
diagonal of the unit vectors in the original directions. -/
theorem norm_mul_finiteGramCoordinate_eq_normalized_inverse_diag
    (S : Finset ι) (hu : ∀ j ∈ S, u j ≠ 0) (i : S) :
    ‖u i.val‖ * finiteGramCoordinate u i.val S =
      Real.sqrt ((Matrix.gram ℂ (fun j : S ↦ ((‖u j.val‖⁻¹ : ℝ) : ℂ) • u j.val))⁻¹ i i).re := by
  let a (j : ι) : ℂ := (‖u j‖⁻¹ : ℝ)
  have ha (j : ι) (hj : j ∈ S) : a j ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr (hu j hj)))
  have h := (norm_mul_finiteGramCoordinate_smul (u := u) a i.val S ha).symm
  have hn : ‖a i.val • u i.val‖ = 1 := by
    rw [norm_smul, show ‖a i.val‖ = ‖u i.val‖⁻¹ by
      simp [a]]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hu _ i.property))
  simpa only [hn, one_mul, finiteGramCoordinate, i.property, dite_eq_left, a] using h

/-- A continuous functional which kills the other vectors in the finite block and
takes a nonzero value `b` at `i` bounds the condition number of that block.
Its values on vectors outside the block are unrestricted. -/
theorem norm_mul_finiteGramCoordinate_le_of_pairings (i : ι) (S : Finset ι)
    (hu : LinearIndependent ℂ (fun j : S ↦ u j.val)) (L : H →L[ℂ] ℂ) {b : ℂ} (hb : b ≠ 0)
    (hdiag : i ∈ S → L (u i) = b) (hoff : ∀ j ∈ S, j ≠ i → L (u j) = 0) :
    ‖u i‖ * finiteGramCoordinate u i S ≤ ‖u i‖ * ‖L‖ / ‖b‖ := by
  classical
  by_cases hi : i ∈ S
  · let l : S := ⟨i, hi⟩
    obtain ⟨c, hc⟩ := (finiteGram_coefficient_isGreatest hu l).1
    let v := ∑ j : S, c j • u j.val
    have hsum : L v = c l * b := by
      change L (∑ j : S, c j • u j.val) = _
      rw [map_sum, Finset.sum_eq_single l]
      · rw [map_smul, hdiag hi, smul_eq_mul]
      · intro j _ hji
        rw [map_smul, hoff j j.property (fun h ↦ hji (Subtype.ext h)), smul_zero]
      · simp
    have hv := L.le_opNorm v
    rw [hsum, norm_mul] at hv
    have hbound : ‖c l‖ / ‖v‖ ≤ ‖L‖ / ‖b‖ := by
      rcases eq_or_lt_of_le (norm_nonneg v) with hn | hn
      · rw [← hn, div_zero]
        positivity
      exact (div_le_div_iff₀ hn (norm_pos_iff.mpr hb)).mpr hv
    rw [finiteGramCoordinate, dite_eq_left hi, ← hc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
  · rw [finiteGramCoordinate, dite_eq_right hi, mul_zero]
    exact div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

end RiemannMasullo
