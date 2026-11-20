import Formalizacao.Whitney1

/-!
# Whitney em `L^p` (M5), parte 2: o resto de Taylor em forma de potência `p`

`∫_I |g - A|^p ≤ L^{2p} ∫_I |G|^p`, com `L = |I|` e `A` a reta tangente de `g` em `c ∈ I`.
-/

open scoped ENNReal
open MeasureTheory Set intervalIntegral

namespace FormalizacaoW

variable {a b : ℝ} {f : ℝ → ℝ}

/-- **Resto de Taylor em `L^p`.** -/
theorem taylor_lp {p : ℝ} (hp : 1 ≤ p) (hf : IntegrableOn f (Icc a b)) (δ : ℝ) {lo hi c : ℝ}
    (hlo : lo ≤ hi) (hc : c ∈ Icc lo hi) :
    ∫⁻ x in Icc lo hi, ‖gs a b f δ x - (gs a b f δ c + gs' a b f δ c * (x - c))‖ₑ ^ p ≤
      ENNReal.ofReal (hi - lo) ^ (2 * p) * ∫⁻ r in Icc lo hi, ‖Gs a b f δ r‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  set L : ℝ := hi - lo with hL
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  set M : ℝ := ∫ r in lo..hi, |Gs a b f δ r| with hM
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg hlo (fun _ _ => abs_nonneg _)
  -- cota pontual em ℝ≥0∞
  have hpt : ∀ x ∈ Icc lo hi,
      ‖gs a b f δ x - (gs a b f δ c + gs' a b f δ c * (x - c))‖ₑ ≤
        ENNReal.ofReal L * ENNReal.ofReal M := by
    intro x hx
    have h := gs_taylor_bound hf δ hlo hc hx
    have hxc : |x - c| ≤ L := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hc.1, hc.2]
    have h2 : |gs a b f δ x - (gs a b f δ c + gs' a b f δ c * (x - c))| ≤ L * M := by
      calc _ = |gs a b f δ x - gs a b f δ c - gs' a b f δ c * (x - c)| := by ring_nf
        _ ≤ |x - c| * M := h
        _ ≤ L * M := mul_le_mul_of_nonneg_right hxc hM0
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hL0]
    exact ENNReal.ofReal_le_ofReal h2
  -- integração da cota
  have h1 : ∫⁻ x in Icc lo hi, ‖gs a b f δ x - (gs a b f δ c + gs' a b f δ c * (x - c))‖ₑ ^ p ≤
      ENNReal.ofReal L * (ENNReal.ofReal L * ENNReal.ofReal M) ^ p := by
    calc _ ≤ ∫⁻ _ in Icc lo hi, (ENNReal.ofReal L * ENNReal.ofReal M) ^ p :=
          setLIntegral_mono' measurableSet_Icc
            (fun x hx => ENNReal.rpow_le_rpow (hpt x hx) hp0.le)
      _ = (ENNReal.ofReal L * ENNReal.ofReal M) ^ p * volume (Icc lo hi) := setLIntegral_const _ _
      _ = _ := by rw [Real.volume_Icc, mul_comm]
  -- `ofReal M = ∫⁻_{Ioc} ‖G‖ₑ`
  have hMl : ENNReal.ofReal M = ∫⁻ r in Ioc lo hi, ‖Gs a b f δ r‖ₑ := by
    have hint : Integrable (Gs a b f δ) (volume.restrict (Ioc lo hi)) :=
      (Gs_integrable hf δ).integrableOn
    have := ofReal_integral_norm_eq_lintegral_enorm hint
    rw [← this, hM, intervalIntegral.integral_of_le hlo]
    simp only [Real.norm_eq_abs]
  -- Hölder
  have hJ := jensen_set hp (S := Ioc lo hi) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (φ := Gs a b f δ) (Gs_integrable hf δ).aemeasurable.restrict
  rw [← hMl, Real.volume_Ioc] at hJ
  have hIcc : ∫⁻ r in Ioc lo hi, ‖Gs a b f δ r‖ₑ ^ p = ∫⁻ r in Icc lo hi, ‖Gs a b f δ r‖ₑ ^ p :=
    setLIntegral_congr Ioc_ae_eq_Icc
  rw [hIcc] at hJ
  refine h1.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  calc ENNReal.ofReal L * (ENNReal.ofReal L ^ p * ENNReal.ofReal M ^ p)
      ≤ ENNReal.ofReal L * (ENNReal.ofReal L ^ p *
          (ENNReal.ofReal L ^ (p - 1) * ∫⁻ r in Icc lo hi, ‖Gs a b f δ r‖ₑ ^ p)) := by
        gcongr
    _ = ENNReal.ofReal L ^ (2 * p) * ∫⁻ r in Icc lo hi, ‖Gs a b f δ r‖ₑ ^ p := by
        rcases hL0.eq_or_lt with h0 | hpos
        · -- `L = 0`
          rw [← h0]
          simp [ENNReal.zero_rpow_of_pos (show 0 < 2 * p by linarith)]
        · have hne0 : ENNReal.ofReal L ≠ 0 := by simpa using hpos
          have hnt : ENNReal.ofReal L ≠ ⊤ := ENNReal.ofReal_ne_top
          have key : ENNReal.ofReal L * (ENNReal.ofReal L ^ p * ENNReal.ofReal L ^ (p - 1)) =
              ENNReal.ofReal L ^ (2 * p) := by
            calc _ = ENNReal.ofReal L ^ (1 : ℝ) * ENNReal.ofReal L ^ (p + (p - 1)) := by
                  rw [ENNReal.rpow_one, ENNReal.rpow_add _ _ hne0 hnt]
              _ = ENNReal.ofReal L ^ (1 + (p + (p - 1))) :=
                  (ENNReal.rpow_add _ _ hne0 hnt).symm
              _ = ENNReal.ofReal L ^ (2 * p) := by congr 1; ring
          rw [← key]
          ring

end FormalizacaoW
