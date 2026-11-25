import research.StripZetaClustering

/-!
# Total logarithmic cost over isolated zeta zeros

Sum first over neighboring zeros. For a fixed source, the isolated centers
are separated on the ordinate line, including clearance from the source
itself. Counting on both sides bounds the total charge from each unit of
source multiplicity by twice the disk radius divided by the separation.
-/

noncomputable section

open Set Metric
open scoped Classical BigOperators

namespace MasulloResearch.StripJets

private theorem card_mul_gap_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {δ r : ℝ} (hr : 0 ≤ r) (hlo : ∀ i ∈ s, δ ≤ f i) (hhi : ∀ i ∈ s, f i ≤ r)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |f i - f j|) :
    s.card * δ ≤ r := by
  induction s using Finset.strongInductionOn generalizing r with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with h | h
    · simpa [h] using hr
    obtain ⟨a, ha, hmax⟩ := s.exists_max_image f h
    have ha₀ := hlo a ha
    have ha₁ := hhi a ha
    have hprev := ih (s.erase a) (Finset.erase_ssubset ha) (r := r-δ) (by linarith)
      (fun i hi ↦ hlo i (Finset.mem_of_mem_erase hi)) (fun i hi ↦ by
        obtain ⟨hne,his⟩ := Finset.mem_erase.mp hi
        have hdiff := hsep a ha i his hne.symm
        rw [abs_of_nonneg (sub_nonneg.mpr (hmax i his))] at hdiff
        linarith) (fun i hi j hj ↦ hsep i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj))
    have hcard : (s.erase a).card + 1 = s.card := Finset.card_erase_add_one ha
    rw [← hcard, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    linarith

private theorem card_mul_gap_le_two_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {δ r : ℝ} (hr : 0 ≤ r) (hlo : ∀ i ∈ s, δ ≤ |f i|) (hhi : ∀ i ∈ s, |f i| ≤ r)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |f i - f j|) :
    s.card * δ ≤ 2*r := by
  let p (i : ι) := 0 ≤ f i
  have hplus := card_mul_gap_le (s.filter p) f hr (fun i hi ↦ by
    obtain ⟨his, hp⟩ := Finset.mem_filter.mp hi
    simpa [abs_of_nonneg hp] using hlo i his) (fun i hi ↦
      (le_abs_self _).trans (hhi i (Finset.mem_filter.mp hi).1))
    (fun i hi j hj ↦ hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1)
  have hminus := card_mul_gap_le (s.filter fun i ↦ ¬p i) (fun i ↦ -f i) hr (fun i hi ↦ by
    obtain ⟨his, hp⟩ := Finset.mem_filter.mp hi
    simpa [abs_of_neg (lt_of_not_ge hp)] using hlo i his) (fun i hi ↦
      (neg_le_abs _).trans (hhi i (Finset.mem_filter.mp hi).1)) (fun i hi j hj hij ↦ by
        simpa only [neg_sub_neg, abs_sub_comm (f j) (f i)] using
          hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
  have hc := Finset.card_filter_add_card_filter_not (s := s) p
  rw [← hc, Nat.cast_add, add_mul]
  linarith

/-- Reversing the sum bounds the total cluster cost over any finite set of
isolated centers. The right side counts the union of their quarter-disks with
source multiplicity. The estimate also covers off-line source zeros. -/
theorem zetaClusterCost_sum_isolated (S : Finset ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ w ∈ S, riemannZeta w = 0)
    (hiso : ∀ w ∈ S, ∀ z : ℂ, riemannZeta z = 0 → z ≠ w → δ ≤ |z.im-w.im|) :
    ∑ w ∈ S, zetaClusterCost w (1/4) ≤
      (∑ z ∈ S.biUnion zetaNeighbors, (analyticOrderNatAt riemannZeta z : ℝ)) * (1/(2*δ)) := by
  let R : ℝ := 1/4
  let Z := S.biUnion zetaNeighbors
  let m (z : ℂ) : ℝ := analyticOrderNatAt riemannZeta z
  let depth (z w : ℂ) := Real.log (R / dist z w)
  let centers (z : ℂ) := S.filter (fun w ↦ z ∈ zetaNeighbors w)
  have hR : 0 < R := by norm_num [R]
  have hdata {z w : ℂ} (hw : w ∈ centers z) :
      w ∈ S ∧ z ≠ w ∧ dist z w ≤ R ∧ riemannZeta z = 0 := by
    obtain ⟨hS,hz⟩ := Finset.mem_filter.mp hw
    exact ⟨hS, mem_zetaNeighbors_iff.mp hz⟩
  have hd {z w : ℂ} (hw : w ∈ centers z) : 0 ≤ depth z w :=
    Real.log_nonneg ((one_le_div (dist_pos.mpr (hdata hw).2.1)).mpr (hdata hw).2.2.1)
  have hone (z : ℂ) : ∑ w ∈ centers z, depth z w ≤ 1/(2*δ) := by
    let U := ∑ w ∈ centers z, depth z w
    have hU : 0 ≤ U := Finset.sum_nonneg fun _ hw ↦ hd hw
    have hmax (w : ℂ) (hw : w ∈ centers z) : depth z w ≤ U :=
      Finset.single_le_sum (fun _ hi ↦ hd hi) hw
    have hcount (u : ℝ) (_ : u ∈ Icc 0 U) :
        (∑ w ∈ centers z, if u ≤ depth z w then (1 : ℝ) else 0) ≤
          (2*R/δ)*Real.exp (-u) + 0 := by
      let A := (centers z).filter (fun w ↦ u ≤ depth z w)
      let f (w : ℂ) := w.im-z.im
      have hcard := card_mul_gap_le_two_mul A f (r := R * Real.exp (-u)) (by positivity)
        (fun w hw ↦ by
          obtain ⟨hwS,hne,_,hz⟩ := hdata (Finset.mem_filter.mp hw).1
          simpa [f, abs_sub_comm] using hiso w hwS z hz hne)
        (fun w hw ↦ by
          obtain ⟨hwc,hu⟩ := Finset.mem_filter.mp hw
          have hp := dist_pos.mpr (hdata hwc).2.1
          have he := (Real.le_log_iff_exp_le (div_pos hR hp)).mp hu
          have hdist : dist z w ≤ R * Real.exp (-u) := by
            rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), mul_comm]
            exact (le_div_iff₀ hp).mp he
          apply le_trans _ hdist
          simpa [f, dist_eq_norm, norm_sub_rev z w] using Complex.abs_im_le_norm (w-z))
        (fun w hw t ht hwt ↦ by
          have hwS := (hdata (Finset.mem_filter.mp hw).1).1
          have htS := (hdata (Finset.mem_filter.mp ht).1).1
          simpa [f] using hiso t htS w (hzero w hwS) hwt)
      have heq : (∑ w ∈ centers z, if u ≤ depth z w then (1 : ℝ) else 0) = A.card := by
        simp [A]
      rw [heq, add_zero]
      calc (A.card : ℝ) ≤ 2*(R*Real.exp (-u))/δ := (le_div_iff₀ hδ).mpr hcard
           _ = _ := by ring
    have htr := truncated_log_sum_le (centers z) (depth z) (fun _ ↦ 1) hU
      (fun _ hw ↦ hd hw) (fun _ _ ↦ zero_le_one) hcount
    simp only [one_mul, zero_mul, add_zero] at htr
    have he := Finset.sum_congr (s₁ := centers z) rfl fun w hw ↦ min_eq_left (hmax w hw)
    rw [he] at htr
    have hcoef : 0 ≤ 2*R/δ := by positivity
    calc _ ≤ _ := htr
         _ ≤ 2*R/δ := by nlinarith [mul_nonneg hcoef (Real.exp_pos (-U)).le]
         _ = _ := by dsimp [R]; ring
  have hrow (w : ℂ) (hw : w ∈ S) : zetaClusterCost w R =
      ∑ z ∈ Z, if z ∈ zetaNeighbors w then m z * depth z w else 0 := by
    rw [← Finset.sum_filter]
    have heq : Z.filter (fun z ↦ z ∈ zetaNeighbors w) = zetaNeighbors w := by
      ext z
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun hz ↦ Finset.mem_biUnion.mpr ⟨w,hw,hz⟩
    rw [heq]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    have hcen : w ∈ centers z := Finset.mem_filter.mpr ⟨hw,hz⟩
    change m z * max 0 (depth z w) = _
    rw [max_eq_right (hd hcen)]
  calc
    _ = ∑ z ∈ Z, ∑ w ∈ S, if z ∈ zetaNeighbors w then m z * depth z w else 0 := by
      rw [← Finset.sum_comm]
      exact Finset.sum_congr rfl hrow
    _ ≤ ∑ z ∈ Z, m z * (1/(2*δ)) := by
      refine Finset.sum_le_sum fun z _ ↦ ?_
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hone z) (Nat.cast_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

/-- Quantitative exceptional-set estimate. Large costs consume at least the
threshold for each exceptional center. -/
theorem zetaClusterCost_large_isolated (S : Finset ℂ) {δ Y : ℝ} (hδ : 0 < δ)
    (hzero : ∀ w ∈ S, riemannZeta w = 0)
    (hiso : ∀ w ∈ S, ∀ z : ℂ, riemannZeta z = 0 → z ≠ w → δ ≤ |z.im-w.im|) :
    ((S.filter fun w ↦ Y < zetaClusterCost w (1/4)).card : ℝ) * Y ≤
      (∑ z ∈ S.biUnion zetaNeighbors, (analyticOrderNatAt riemannZeta z : ℝ)) * (1/(2*δ)) := by
  let bad := S.filter (fun w ↦ Y < zetaClusterCost w (1/4))
  calc
    _ = ∑ _w ∈ bad, Y := by simp [bad]
    _ ≤ ∑ w ∈ bad, zetaClusterCost w (1/4) := Finset.sum_le_sum fun _ hw ↦ (Finset.mem_filter.mp hw).2.le
    _ ≤ ∑ w ∈ S, zetaClusterCost w (1/4) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
      intro w _ _
      exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (le_max_left ..)
    _ ≤ _ := zetaClusterCost_sum_isolated S hδ hzero hiso

/-- A finite upper bound for the number of simple isolated zeros with small
ordinary derivative. The mean input comes from the classical local product.
No estimate for the number of zeros in shrinking windows is needed. -/
theorem zetaDerivative_small_isolated (S : Finset ℂ) {δ Y B : ℝ} (hδ : 0 < δ) (hY : 0 ≤ Y)
    (hzero : ∀ w ∈ S, riemannZeta w = 0)
    (hsimple : ∀ w ∈ S, analyticOrderAt riemannZeta w = 1)
    (hheight : ∀ w ∈ S, 1 ≤ |w.im|)
    (hiso : ∀ w ∈ S, ∀ z : ℂ, riemannZeta z = 0 → z ≠ w → δ ≤ |z.im-w.im|)
    (hmean : ∀ w ∈ S, -B ≤ Real.circleAverage (fun z ↦ Real.log ‖riemannZeta z‖) w (1/4)) :
    ((S.filter fun w ↦ ‖deriv riemannZeta w‖ < Real.exp (-(B+Y))).card : ℝ) * Y ≤
      (∑ z ∈ S.biUnion zetaNeighbors, (analyticOrderNatAt riemannZeta z : ℝ)) * (1/(2*δ)) := by
  apply le_trans _ (zetaClusterCost_large_isolated S (Y := Y) hδ hzero hiso)
  apply mul_le_mul_of_nonneg_right _ hY
  exact_mod_cast Finset.card_le_card (show S.filter (fun w ↦ ‖deriv riemannZeta w‖ <
      Real.exp (-(B+Y))) ⊆ S.filter (fun w ↦ Y < zetaClusterCost w (1/4)) from by
    intro w hw
    obtain ⟨hwS,hsmall⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_filter.mpr ⟨hwS, ?_⟩
    have ht := hheight w hwS
    have hne : w ≠ 1 := by rintro rfl; norm_num at ht
    have hn : analyticOrderAt riemannZeta w = (1 : ℕ) := hsimple w hwS
    have hd := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticOn_riemannZeta w hne)).mp hn).2
    simp only [iteratedDeriv_one] at hd
    have hl := Real.log_lt_log (norm_pos_iff.mpr hd) hsmall
    rw [Real.log_exp] at hl
    have h := hmean w hwS
    rw [zeta_circleAverage_eq_cluster_add_coeff ht hn] at h
    simp only [taylorCoeff, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one, one_mul] at h
    have := Real.log_nonpos (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num)
    linarith)

end MasulloResearch.StripJets
