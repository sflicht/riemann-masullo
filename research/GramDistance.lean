import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# A finite Gram coordinate against a distance

The finite Gram coordinate of `u i` in a block `S` is the largest ratio
`‖c i‖ / ‖∑ c j • u j‖` over coefficients supported on `S`. Dividing by `c i`
exhibits `u i` minus a combination of the other vectors of the block. Any
distance from `u i` to a subspace containing those vectors is therefore at most
the reciprocal coordinate. The statement transports the distance along an
isometric linear map, so that it can be read in a space of functionals.
-/

noncomputable section

open Set

namespace MasulloResearch.StripBlocks

open RiemannMasullo

/-- Let `T` be an isometric linear map with `T (Λ j) = u j`, and let `P` be a
subspace containing `Λ j` for every member `j ≠ i` of the block `S`. Then the
finite Gram coordinate of `u i` in `S`, times the distance from `Λ i` to `P`,
is at most one. -/
theorem finiteGramCoordinate_mul_infDist_le_one {ι E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : E →ₗ[ℂ] H) (hT : Isometry T) (Λ : ι → E) {u : ι → H} (hΛ : ∀ j, T (Λ j) = u j)
    (hu : LinearIndependent ℂ u) (i : ι) (S : Finset ι) (P : Submodule ℂ E)
    (hP : ∀ j ∈ S, j ≠ i → Λ j ∈ P) :
    finiteGramCoordinate u i S * Metric.infDist (Λ i) (P : Set E) ≤ 1 := by
  classical
  obtain ⟨c, hc, hcval⟩ := (finiteGramCoordinate_isGreatest hu i S).1
  have hc' : c.support ⊆ S := hc
  rw [← hcval]
  change ‖c i‖ / ‖Finsupp.linearCombination ℂ u c‖ * Metric.infDist (Λ i) (P : Set E) ≤ 1
  have hd0 : 0 ≤ Metric.infDist (Λ i) (P : Set E) := Metric.infDist_nonneg
  rcases eq_or_ne (c i) 0 with h0 | h0
  · simp [h0]
  rcases eq_or_ne (Finsupp.linearCombination ℂ u c) 0 with hy0 | hy0
  · simp [hy0]
  let G : E := Finsupp.linearCombination ℂ Λ c
  have hTG : T G = Finsupp.linearCombination ℂ u c := by
    simp only [G, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hΛ]
  have hsplit : G = c i • Λ i + ∑ j ∈ c.support.erase i, c j • Λ j := by
    simp only [G, Finsupp.linearCombination_apply, Finsupp.sum]
    exact (Finset.add_sum_erase c.support (fun j ↦ c j • Λ j)
      (Finsupp.mem_support_iff.mpr h0)).symm
  let g : E := -((c i)⁻¹ • ∑ j ∈ c.support.erase i, c j • Λ j)
  have hgP : g ∈ P := by
    refine P.neg_mem (P.smul_mem _ (P.sum_mem fun j hj ↦ ?_))
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
    exact P.smul_mem _ (hP j (hc' hjs) hji)
  have hdiff : Λ i - g = (c i)⁻¹ • G := by
    rw [hsplit, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul]
    simp only [g, sub_neg_eq_add]
  have hnorm : ‖Λ i - g‖ = ‖c i‖⁻¹ * ‖Finsupp.linearCombination ℂ u c‖ := by
    rw [hdiff, norm_smul, norm_inv, ← hTG, (AddMonoidHomClass.isometry_iff_norm T).mp hT G]
  have hd : Metric.infDist (Λ i) (P : Set E) ≤ ‖c i‖⁻¹ * ‖Finsupp.linearCombination ℂ u c‖ := by
    rw [← hnorm, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem hgP
  have hci : 0 < ‖c i‖ := norm_pos_iff.mpr h0
  have hyp : 0 < ‖Finsupp.linearCombination ℂ u c‖ := norm_pos_iff.mpr hy0
  calc ‖c i‖ / ‖Finsupp.linearCombination ℂ u c‖ * Metric.infDist (Λ i) (P : Set E)
      ≤ ‖c i‖ / ‖Finsupp.linearCombination ℂ u c‖ *
          (‖c i‖⁻¹ * ‖Finsupp.linearCombination ℂ u c‖) := by gcongr
    _ = 1 := by field_simp

end MasulloResearch.StripBlocks
