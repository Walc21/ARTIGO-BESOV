import Formalizacao.Whitney4

/-!
# Whitney em `L^p` (M5), parte 5: translação e faixas laterais
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoW

/-- translação de integrais em intervalos -/
lemma lintegral_Icc_shift (φ : ℝ → ℝ≥0∞) (u v d : ℝ) :
    ∫⁻ x in Icc u v, φ (x + d) = ∫⁻ y in Icc (u + d) (v + d), φ y := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) d
  have := hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.addRight d).measurableEmbedding φ
    (Icc (u + d) (v + d))
  simpa [Set.preimage_add_const_Icc] using this

lemma lintegral_Icc_shift' (φ : ℝ → ℝ≥0∞) (u v d : ℝ) :
    ∫⁻ x in Icc u v, φ (x - d) = ∫⁻ y in Icc (u - d) (v - d), φ y := by
  have := lintegral_Icc_shift φ u v (-d)
  simpa [sub_eq_add_neg] using this

/-- `(x+y+z)^p ≤ 4^{p-1}(x^p+y^p+z^p)` -/
lemma rpow_add3_le {p : ℝ} (hp : 1 ≤ p) (x y z : ℝ≥0∞) :
    (x + y + z) ^ p ≤ 2 ^ (2 * (p - 1)) * (x ^ p + y ^ p + z ^ p) := by
  have h2 : (1 : ℝ≥0∞) ≤ 2 ^ (p - 1) := by
    simpa using ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (show (0 : ℝ) ≤ p - 1 by linarith)
  have e : (2 : ℝ≥0∞) ^ (2 * (p - 1)) = 2 ^ (p - 1) * 2 ^ (p - 1) := by
    rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]; congr 1; ring
  calc (x + y + z) ^ p ≤ 2 ^ (p - 1) * ((x + y) ^ p + z ^ p) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    _ ≤ 2 ^ (p - 1) * (2 ^ (p - 1) * (x ^ p + y ^ p) + z ^ p) := by
        gcongr; exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    _ ≤ 2 ^ (p - 1) * (2 ^ (p - 1) * (x ^ p + y ^ p) + 2 ^ (p - 1) * z ^ p) := by
        gcongr; exact le_mul_of_one_le_left (zero_le _) h2
    _ = 2 ^ (2 * (p - 1)) * (x ^ p + y ^ p + z ^ p) := by rw [e]; ring

/-- **Faixa esquerda.** Se `u x = 2 u(x+δ) - u(x+2δ) + w(x+δ)`, então
`∫_{[a,a+δ]} |u|^p ≤ 4^{p-1} (2^p ∫_{[a+δ,a+2δ]} |u|^p + ∫_{[a+2δ,a+3δ]} |u|^p
  + ∫_{[a+δ,a+2δ]} |w|^p)`. -/
lemma strip_left {p : ℝ} (hp : 1 ≤ p) {u w : ℝ → ℝ} (hu : Measurable u) (hw : Measurable w)
    {δ : ℝ} (a : ℝ) (hid : ∀ x, u x = 2 * u (x + δ) - u (x + 2 * δ) + w (x + δ)) :
    ∫⁻ x in Icc a (a + δ), ‖u x‖ₑ ^ p ≤ 2 ^ (2 * (p - 1)) *
      (2 ^ p * (∫⁻ y in Icc (a + δ) (a + δ + δ), ‖u y‖ₑ ^ p) +
       (∫⁻ y in Icc (a + 2 * δ) (a + 2 * δ + δ), ‖u y‖ₑ ^ p) +
       (∫⁻ y in Icc (a + δ) (a + δ + δ), ‖w y‖ₑ ^ p)) := by
  have hp0 : 0 < p := by linarith
  have pt : ∀ x, ‖u x‖ₑ ^ p ≤ 2 ^ (2 * (p - 1)) *
      (2 ^ p * ‖u (x + δ)‖ₑ ^ p + ‖u (x + 2 * δ)‖ₑ ^ p + ‖w (x + δ)‖ₑ ^ p) := by
    intro x
    have h1 : ‖u x‖ₑ ≤ 2 * ‖u (x + δ)‖ₑ + ‖u (x + 2 * δ)‖ₑ + ‖w (x + δ)‖ₑ := by
      rw [hid x]
      calc ‖2 * u (x + δ) - u (x + 2 * δ) + w (x + δ)‖ₑ
          ≤ ‖2 * u (x + δ) - u (x + 2 * δ)‖ₑ + ‖w (x + δ)‖ₑ := enorm_add_le _ _
        _ ≤ (‖2 * u (x + δ)‖ₑ + ‖u (x + 2 * δ)‖ₑ) + ‖w (x + δ)‖ₑ := by
            gcongr; exact enorm_sub_le
        _ = 2 * ‖u (x + δ)‖ₑ + ‖u (x + 2 * δ)‖ₑ + ‖w (x + δ)‖ₑ := by
            have h2n : ‖(2 : ℝ)‖ₑ = 2 := by
              rw [Real.enorm_eq_ofReal_abs]; norm_num
            rw [enorm_mul, h2n]
    calc ‖u x‖ₑ ^ p ≤ (2 * ‖u (x + δ)‖ₑ + ‖u (x + 2 * δ)‖ₑ + ‖w (x + δ)‖ₑ) ^ p :=
          ENNReal.rpow_le_rpow h1 hp0.le
      _ ≤ 2 ^ (2 * (p - 1)) * ((2 * ‖u (x + δ)‖ₑ) ^ p + ‖u (x + 2 * δ)‖ₑ ^ p
            + ‖w (x + δ)‖ₑ ^ p) := rpow_add3_le hp _ _ _
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  have mu : Measurable (fun y => ‖u y‖ₑ ^ p) := hu.enorm.pow_const p
  have mw : Measurable (fun y => ‖w y‖ₑ ^ p) := hw.enorm.pow_const p
  have m1 : Measurable (fun x : ℝ => ‖u (x + δ)‖ₑ ^ p) := mu.comp (by fun_prop)
  have m2 : Measurable (fun x : ℝ => ‖u (x + 2 * δ)‖ₑ ^ p) := mu.comp (by fun_prop)
  have m3 : Measurable (fun x : ℝ => ‖w (x + δ)‖ₑ ^ p) := mw.comp (by fun_prop)
  have hc2 : (2 : ℝ≥0∞) ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le (by norm_num)
  have s1 := lintegral_Icc_shift (fun y => ‖u y‖ₑ ^ p) a (a + δ) δ
  have s2 := lintegral_Icc_shift (fun y => ‖u y‖ₑ ^ p) a (a + δ) (2 * δ)
  have s3 := lintegral_Icc_shift (fun y => ‖w y‖ₑ ^ p) a (a + δ) δ
  have e2 : a + δ + 2 * δ = a + 2 * δ + δ := by ring
  rw [e2] at s2
  calc ∫⁻ x in Icc a (a + δ), ‖u x‖ₑ ^ p
      ≤ ∫⁻ x in Icc a (a + δ), 2 ^ (2 * (p - 1)) *
          (2 ^ p * ‖u (x + δ)‖ₑ ^ p + ‖u (x + 2 * δ)‖ₑ ^ p + ‖w (x + δ)‖ₑ ^ p) :=
        lintegral_mono pt
    _ = 2 ^ (2 * (p - 1)) * ∫⁻ x in Icc a (a + δ),
          (2 ^ p * ‖u (x + δ)‖ₑ ^ p + ‖u (x + 2 * δ)‖ₑ ^ p + ‖w (x + δ)‖ₑ ^ p) :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by nlinarith) (by norm_num))
    _ = _ := by
        congr 1
        rw [lintegral_add_left ((m1.const_mul _).add m2), lintegral_add_left (m1.const_mul _),
          lintegral_const_mul' _ _ hc2]
        rw [s1, s2, s3]

/-- **Faixa direita.** Se `u x = 2 u(x-δ) - u(x-2δ) + w(x-δ)`, então
`∫_{[b-δ,b]} |u|^p ≤ 4^{p-1} (2^p ∫_{[b-2δ,b-δ]} |u|^p + ∫_{[b-3δ,b-2δ]} |u|^p
  + ∫_{[b-2δ,b-δ]} |w|^p)`. -/
lemma strip_right {p : ℝ} (hp : 1 ≤ p) {u w : ℝ → ℝ} (hu : Measurable u) (hw : Measurable w)
    {δ : ℝ} (b : ℝ) (hid : ∀ x, u x = 2 * u (x - δ) - u (x - 2 * δ) + w (x - δ)) :
    ∫⁻ x in Icc (b - δ) b, ‖u x‖ₑ ^ p ≤ 2 ^ (2 * (p - 1)) *
      (2 ^ p * (∫⁻ y in Icc (b - δ - δ) (b - δ), ‖u y‖ₑ ^ p) +
       (∫⁻ y in Icc (b - δ - 2 * δ) (b - 2 * δ), ‖u y‖ₑ ^ p) +
       (∫⁻ y in Icc (b - δ - δ) (b - δ), ‖w y‖ₑ ^ p)) := by
  have hp0 : 0 < p := by linarith
  have pt : ∀ x, ‖u x‖ₑ ^ p ≤ 2 ^ (2 * (p - 1)) *
      (2 ^ p * ‖u (x - δ)‖ₑ ^ p + ‖u (x - 2 * δ)‖ₑ ^ p + ‖w (x - δ)‖ₑ ^ p) := by
    intro x
    have h1 : ‖u x‖ₑ ≤ 2 * ‖u (x - δ)‖ₑ + ‖u (x - 2 * δ)‖ₑ + ‖w (x - δ)‖ₑ := by
      rw [hid x]
      calc ‖2 * u (x - δ) - u (x - 2 * δ) + w (x - δ)‖ₑ
          ≤ ‖2 * u (x - δ) - u (x - 2 * δ)‖ₑ + ‖w (x - δ)‖ₑ := enorm_add_le _ _
        _ ≤ (‖2 * u (x - δ)‖ₑ + ‖u (x - 2 * δ)‖ₑ) + ‖w (x - δ)‖ₑ := by
            gcongr; exact enorm_sub_le
        _ = 2 * ‖u (x - δ)‖ₑ + ‖u (x - 2 * δ)‖ₑ + ‖w (x - δ)‖ₑ := by
            have h2n : ‖(2 : ℝ)‖ₑ = 2 := by
              rw [Real.enorm_eq_ofReal_abs]; norm_num
            rw [enorm_mul, h2n]
    calc ‖u x‖ₑ ^ p ≤ (2 * ‖u (x - δ)‖ₑ + ‖u (x - 2 * δ)‖ₑ + ‖w (x - δ)‖ₑ) ^ p :=
          ENNReal.rpow_le_rpow h1 hp0.le
      _ ≤ 2 ^ (2 * (p - 1)) * ((2 * ‖u (x - δ)‖ₑ) ^ p + ‖u (x - 2 * δ)‖ₑ ^ p
            + ‖w (x - δ)‖ₑ ^ p) := rpow_add3_le hp _ _ _
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  have mu : Measurable (fun y => ‖u y‖ₑ ^ p) := hu.enorm.pow_const p
  have mw : Measurable (fun y => ‖w y‖ₑ ^ p) := hw.enorm.pow_const p
  have m1 : Measurable (fun x : ℝ => ‖u (x - δ)‖ₑ ^ p) := mu.comp (by fun_prop)
  have m2 : Measurable (fun x : ℝ => ‖u (x - 2 * δ)‖ₑ ^ p) := mu.comp (by fun_prop)
  have m3 : Measurable (fun x : ℝ => ‖w (x - δ)‖ₑ ^ p) := mw.comp (by fun_prop)
  have hc2 : (2 : ℝ≥0∞) ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le (by norm_num)
  have s1 := lintegral_Icc_shift' (fun y => ‖u y‖ₑ ^ p) (b - δ) b δ
  have s2 := lintegral_Icc_shift' (fun y => ‖u y‖ₑ ^ p) (b - δ) b (2 * δ)
  have s3 := lintegral_Icc_shift' (fun y => ‖w y‖ₑ ^ p) (b - δ) b δ
  have e2 : b - δ - 2 * δ = b - 2 * δ - δ := by ring
  calc ∫⁻ x in Icc (b - δ) b, ‖u x‖ₑ ^ p
      ≤ ∫⁻ x in Icc (b - δ) b, 2 ^ (2 * (p - 1)) *
          (2 ^ p * ‖u (x - δ)‖ₑ ^ p + ‖u (x - 2 * δ)‖ₑ ^ p + ‖w (x - δ)‖ₑ ^ p) :=
        lintegral_mono pt
    _ = 2 ^ (2 * (p - 1)) * ∫⁻ x in Icc (b - δ) b,
          (2 ^ p * ‖u (x - δ)‖ₑ ^ p + ‖u (x - 2 * δ)‖ₑ ^ p + ‖w (x - δ)‖ₑ ^ p) :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by nlinarith) (by norm_num))
    _ = _ := by
        congr 1
        rw [lintegral_add_left ((m1.const_mul _).add m2), lintegral_add_left (m1.const_mul _),
          lintegral_const_mul' _ _ hc2]
        rw [s1, s2, s3]

end FormalizacaoW
