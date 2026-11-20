import Formalizacao.Corollary54

/-!
# Whitney em `L^p` (M5), parte 0: desigualdades básicas

Hölder/Jensen em conjuntos de medida finita, na forma de potências `p`-ésimas em `ℝ≥0∞`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoW

/-- **Jensen/Hölder em um conjunto.** Para `p ≥ 1`, `φ` mensurável e `S` de medida finita:
`(∫_S ‖φ‖)^p ≤ |S|^{p-1} ∫_S ‖φ‖^p`. -/
theorem jensen_set {p : ℝ} (hp : 1 ≤ p) {S : Set ℝ} (hS : volume S ≠ ⊤) {φ : ℝ → ℝ}
    (hφ : AEMeasurable φ (volume.restrict S)) :
    (∫⁻ x in S, ‖φ x‖ₑ) ^ p ≤ (volume S) ^ (p - 1) * ∫⁻ x in S, ‖φ x‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  set μ : Measure ℝ := volume.restrict S with hμ
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hS⟩
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hmeas : AEStronglyMeasurable φ μ := hφ.aestronglyMeasurable
  have key := eLpNorm_le_eLpNorm_mul_rpow_measure_univ h1 hmeas
  rw [eLpNorm_one_eq_lintegral_enorm] at key
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpow := ENNReal.rpow_le_rpow key hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le] at hpow
  have hL : eLpNorm φ (ENNReal.ofReal p) μ ^ p = ∫⁻ x in S, ‖φ x‖ₑ ^ p := by
    simpa [hμ] using FormalizacaoCor.Np_rpow_eq hp φ S
  rw [hL] at hpow
  have hexp : (μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal)) ^ p
      = (volume S) ^ (p - 1) := by
    rw [← ENNReal.rpow_mul, hpr]
    have : (1 / (1 : ℝ≥0∞).toReal - 1 / p) * p = p - 1 := by
      simp only [ENNReal.toReal_one, div_one]
      field_simp
    rw [this, hμ, Measure.restrict_apply_univ]
  rw [hexp] at hpow
  rw [mul_comm]
  exact hpow

end FormalizacaoW
