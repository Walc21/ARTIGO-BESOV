import Mathlib

/-!
# Projeção afim local nos extremos (M4, Lema 5.1 do artigo)

Para um intervalo `I = [a, a+ℓ]`, `ℓ > 0`, o núcleo do funcional `h ↦ (P_I h)(e)` no
extremo `e`, onde `P_I` é a projeção ortogonal de `L²(I)` sobre as funções afins, é

* `kL a ℓ y = ℓ⁻¹ (4 - 6u)` para `e = a` (`u = (y-a)/ℓ`),
* `kR a ℓ y = ℓ⁻¹ (6u - 2)` para `e = a + ℓ`.

Aqui o núcleo é tomado diretamente, sem passar pelo produto interno de `L²`. Provam-se:

* `abs_kL_le`, `abs_kR_le`: `|k| ≤ 4/ℓ` em `I` (a cota pontual que dá a cota `L^p` do Lema 5.1 por Hölder);
* `integral_kL_mul_affine`, `integral_kR_mul_affine`: o funcional reproduz funções afins,
  `∫_I k(y)(α+βy) dy = α + β a` (extremo `a`) e `= α + β(a+ℓ)` (extremo `a+ℓ`).

Não formalizado aqui: a cota `L^p` (Hölder) e a cota `L^∞` com a constante `2`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoQuasi

/-- Núcleo no extremo esquerdo `a`. -/
noncomputable def kL (a ℓ y : ℝ) : ℝ := (4 - 6 * ((y - a) / ℓ)) / ℓ

/-- Núcleo no extremo direito `a + ℓ`. -/
noncomputable def kR (a ℓ y : ℝ) : ℝ := (6 * ((y - a) / ℓ) - 2) / ℓ

/-- Cota pontual `|k_a| ≤ 4/ℓ` em `I = [a, a+ℓ]`. -/
theorem abs_kL_le {a ℓ y : ℝ} (hℓ : 0 < ℓ) (hy : y ∈ Icc a (a + ℓ)) :
    |kL a ℓ y| ≤ 4 / ℓ := by
  obtain ⟨h1, h2⟩ := hy
  have ht0 : 0 ≤ (y - a) / ℓ := div_nonneg (by linarith) hℓ.le
  have ht1 : (y - a) / ℓ ≤ 1 := by rw [div_le_one hℓ]; linarith
  unfold kL
  rw [abs_div, abs_of_pos hℓ]
  apply div_le_div_of_nonneg_right _ hℓ.le
  rw [abs_le]
  constructor <;> linarith

/-- Cota pontual `|k_{a+ℓ}| ≤ 4/ℓ` em `I = [a, a+ℓ]`. -/
theorem abs_kR_le {a ℓ y : ℝ} (hℓ : 0 < ℓ) (hy : y ∈ Icc a (a + ℓ)) :
    |kR a ℓ y| ≤ 4 / ℓ := by
  obtain ⟨h1, h2⟩ := hy
  have ht0 : 0 ≤ (y - a) / ℓ := div_nonneg (by linarith) hℓ.le
  have ht1 : (y - a) / ℓ ≤ 1 := by rw [div_le_one hℓ]; linarith
  unfold kR
  rw [abs_div, abs_of_pos hℓ]
  apply div_le_div_of_nonneg_right _ hℓ.le
  rw [abs_le]
  constructor <;> linarith

/-- Reprodução de funções afins pelo núcleo no extremo `a`:
`∫_a^{a+ℓ} k_a(y)(α+βy) dy = α + β a`. -/
theorem integral_kL_mul_affine (a ℓ α β : ℝ) (hℓ : ℓ ≠ 0) :
    ∫ y in a..a + ℓ, kL a ℓ y * (α + β * y) = α + β * a := by
  set A : ℝ := α + β * a with hA
  set B : ℝ := β * ℓ with hB
  set K : ℝ → ℝ := fun t => 4 * A * t + (2 * B - 3 * A) * t ^ 2 - 2 * B * t ^ 3 with hKdef
  have hK : ∀ t : ℝ, HasDerivAt K (4 * A + 2 * (2 * B - 3 * A) * t - 6 * B * t ^ 2) t := by
    intro t
    have h := (((hasDerivAt_id t).const_mul (4 * A)).add
      ((hasDerivAt_pow 2 t).const_mul (2 * B - 3 * A))).sub
      ((hasDerivAt_pow 3 t).const_mul (2 * B))
    convert h using 1
    simp only [id, Nat.cast_ofNat]
    ring
  have hF : ∀ y ∈ uIcc a (a + ℓ),
      HasDerivAt (fun y => K ((y - a) / ℓ)) (kL a ℓ y * (α + β * y)) y := by
    intro y _
    have ht : HasDerivAt (fun y => (y - a) / ℓ) (1 / ℓ) y :=
      ((hasDerivAt_id y).sub_const a).div_const ℓ
    have hc := (hK ((y - a) / ℓ)).comp y ht
    convert hc using 1
    unfold kL
    have hyeq : α + β * y = A + B * ((y - a) / ℓ) := by
      rw [hA, hB]
      field_simp
      ring
    rw [hyeq]
    field_simp
    ring
  have hint : Continuous fun y => kL a ℓ y * (α + β * y) := by
    unfold kL
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hint.intervalIntegrable _ _)]
  have h1 : (a + ℓ - a) / ℓ = 1 := by field_simp; ring
  have h0 : (a - a) / ℓ = 0 := by simp
  simp only [h1, h0, hKdef]
  rw [hA]
  ring

/-- Reprodução de funções afins pelo núcleo no extremo `a + ℓ`:
`∫_a^{a+ℓ} k_{a+ℓ}(y)(α+βy) dy = α + β(a+ℓ)`. -/
theorem integral_kR_mul_affine (a ℓ α β : ℝ) (hℓ : ℓ ≠ 0) :
    ∫ y in a..a + ℓ, kR a ℓ y * (α + β * y) = α + β * (a + ℓ) := by
  set A : ℝ := α + β * a with hA
  set B : ℝ := β * ℓ with hB
  set K : ℝ → ℝ := fun t => -2 * A * t + (3 * A - B) * t ^ 2 + 2 * B * t ^ 3 with hKdef
  have hK : ∀ t : ℝ, HasDerivAt K (-2 * A + 2 * (3 * A - B) * t + 6 * B * t ^ 2) t := by
    intro t
    have h := (((hasDerivAt_id t).const_mul (-2 * A)).add
      ((hasDerivAt_pow 2 t).const_mul (3 * A - B))).add
      ((hasDerivAt_pow 3 t).const_mul (2 * B))
    convert h using 1
    simp only [id, Nat.cast_ofNat]
    ring
  have hF : ∀ y ∈ uIcc a (a + ℓ),
      HasDerivAt (fun y => K ((y - a) / ℓ)) (kR a ℓ y * (α + β * y)) y := by
    intro y _
    have ht : HasDerivAt (fun y => (y - a) / ℓ) (1 / ℓ) y :=
      ((hasDerivAt_id y).sub_const a).div_const ℓ
    have hc := (hK ((y - a) / ℓ)).comp y ht
    convert hc using 1
    unfold kR
    have hyeq : α + β * y = A + B * ((y - a) / ℓ) := by
      rw [hA, hB]
      field_simp
      ring
    rw [hyeq]
    field_simp
    ring
  have hint : Continuous fun y => kR a ℓ y * (α + β * y) := by
    unfold kR
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hint.intervalIntegrable _ _)]
  have h1 : (a + ℓ - a) / ℓ = 1 := by field_simp; ring
  have h0 : (a - a) / ℓ = 0 := by simp
  simp only [h1, h0, hKdef]
  rw [hA, hB]
  ring

/-- **Cota de Hölder do Lema 5.1.** Se `|k| ≤ 4/ℓ` em `I = [a, a+ℓ]`, então
`|∫_I k h| ≤ 4 ℓ^{-1/p} ‖h‖_{L^p(I)}`, para `p ≥ 1`. -/
theorem abs_integral_kernel_le {a ℓ : ℝ} (hℓ : 0 < ℓ) {k h : ℝ → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hk : ∀ y ∈ Icc a (a + ℓ), |k y| ≤ 4 / ℓ) (hkm : Measurable k)
    (hhm : AEStronglyMeasurable h (volume.restrict (Icc a (a + ℓ))))
    (hfin : eLpNorm h (ENNReal.ofReal p) (volume.restrict (Icc a (a + ℓ))) < ⊤) :
    |∫ y in Icc a (a + ℓ), k y * h y| ≤
      4 * ℓ ^ (-(1 / p)) *
        (eLpNorm h (ENNReal.ofReal p) (volume.restrict (Icc a (a + ℓ)))).toReal := by
  set μ : Measure ℝ := volume.restrict (Icc a (a + ℓ)) with hμdef
  have hμu : μ Set.univ = ENNReal.ofReal ℓ := by
    rw [hμdef, Measure.restrict_apply_univ, Real.volume_Icc]
    congr 1
    ring
  have hpreal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  -- Hölder: eLpNorm h 1 μ ≤ eLpNorm h p μ · μ(I)^{1 - 1/p}
  have hholder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq hhm
  rw [ENNReal.toReal_one, hpreal, hμu] at hholder
  have hexp0 : (0 : ℝ) ≤ 1 / 1 - 1 / p := by
    have : 1 / p ≤ 1 := by rw [div_le_one (by linarith)]; exact hp
    linarith
  have hrpow_lt : ENNReal.ofReal ℓ ^ (1 / (1 : ℝ) - 1 / p) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg hexp0 ENNReal.ofReal_ne_top
  have hL1lt : eLpNorm h 1 μ < ⊤ :=
    lt_of_le_of_lt hholder (ENNReal.mul_lt_top hfin hrpow_lt)
  have hL1 : MemLp h 1 μ := ⟨hhm, hL1lt⟩
  have hint : Integrable (fun y => (4 / ℓ) * ‖h y‖) μ :=
    (hL1.integrable le_rfl).norm.const_mul (4 / ℓ)
  -- |∫ k h| ≤ ∫ (4/ℓ)|h|
  have hbound : |∫ y in Icc a (a + ℓ), k y * h y| ≤ ∫ y, (4 / ℓ) * ‖h y‖ ∂μ := by
    have hae : ∀ᵐ y ∂μ, ‖k y * h y‖ ≤ (4 / ℓ) * ‖h y‖ := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hk y hy) (norm_nonneg _)
    have := norm_integral_le_of_norm_le hint hae
    simpa [Real.norm_eq_abs] using this
  rw [integral_const_mul, integral_norm_eq_lintegral_enorm hhm] at hbound
  -- ∫⁻ ‖h‖ₑ = eLpNorm h 1 μ, e a cota de Hölder em `ℝ`
  have hlin : (∫⁻ y, ‖h y‖ₑ ∂μ) = eLpNorm h 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm]
  rw [hlin] at hbound
  have hreal : (eLpNorm h 1 μ).toReal ≤
      (eLpNorm h (ENNReal.ofReal p) μ).toReal * ℓ ^ (1 / (1 : ℝ) - 1 / p) := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ne_top_of_lt hfin)
      (ENNReal.rpow_ne_top_of_nonneg hexp0 ENNReal.ofReal_ne_top)) hholder
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hℓ.le] at h1
    exact h1
  have hℓ1 : ℓ ^ (1 / (1 : ℝ) - 1 / p) = ℓ / ℓ ^ (1 / p) := by
    rw [show 1 / (1 : ℝ) - 1 / p = 1 - 1 / p by norm_num, Real.rpow_sub hℓ, Real.rpow_one]
  have hneg : ℓ ^ (-(1 / p)) = (ℓ ^ (1 / p))⁻¹ := Real.rpow_neg hℓ.le _
  have hpos : 0 < ℓ ^ (1 / p) := Real.rpow_pos_of_pos hℓ _
  calc |∫ y in Icc a (a + ℓ), k y * h y|
      ≤ 4 / ℓ * (eLpNorm h 1 μ).toReal := hbound
    _ ≤ 4 / ℓ * ((eLpNorm h (ENNReal.ofReal p) μ).toReal * ℓ ^ (1 / (1 : ℝ) - 1 / p)) :=
        mul_le_mul_of_nonneg_left hreal (by positivity)
    _ = 4 * ℓ ^ (-(1 / p)) * (eLpNorm h (ENNReal.ofReal p) μ).toReal := by
        rw [hℓ1, hneg]
        field_simp

/-- Integral de `|k_a|` no intervalo: `∫_I |k_a| = 5/3 ≤ 2` (mudança de sinal em `a + 2ℓ/3`). -/
theorem integral_abs_kL (a ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∫ y in Icc a (a + ℓ), |kL a ℓ y| = 5 / 3 := by
  set c : ℝ := a + 2 * ℓ / 3 with hc
  set F : ℝ → ℝ := fun y => (4 * (y - a) - 3 * (y - a) ^ 2 / ℓ) / ℓ with hF
  have hderiv : ∀ y, HasDerivAt F (kL a ℓ y) y := by
    intro y
    have h := ((((hasDerivAt_id y).sub_const a).const_mul 4).sub
      ((((hasDerivAt_id y).sub_const a).pow 2).const_mul (3 / ℓ))).div_const ℓ
    convert h using 1
    all_goals first
      | (funext x; simp only [hF, id, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]; ring)
      | (unfold kL; simp only [id]; norm_num; field_simp; ring)
  have hcont : Continuous fun y => kL a ℓ y := by unfold kL; fun_prop
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hc1 : a ≤ c := by rw [hc]; nlinarith
  have hc2 : c ≤ a + ℓ := by rw [hc]; nlinarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := c) (c := a + ℓ)
    (hcont.abs.intervalIntegrable _ _) (hcont.abs.intervalIntegrable _ _)]
  have hL : ∫ y in a..c, |kL a ℓ y| = ∫ y in a..c, kL a ℓ y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hc1] at hy
    have hq : (y - a) / ℓ ≤ 2 / 3 := by
      rw [div_le_iff₀ hℓ]
      have := hy.2
      rw [hc] at this
      linarith
    have h0 : 0 ≤ kL a ℓ y := by
      unfold kL
      exact div_nonneg (by linarith) hℓ.le
    simp only
    exact abs_of_nonneg h0
  have hR : ∫ y in c..a + ℓ, |kL a ℓ y| = ∫ y in c..a + ℓ, -kL a ℓ y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hc2] at hy
    have hq : 2 / 3 ≤ (y - a) / ℓ := by
      rw [le_div_iff₀ hℓ]
      have := hy.1
      rw [hc] at this
      linarith
    have h0 : kL a ℓ y ≤ 0 := by
      unfold kL
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hℓ.le
    simp only
    exact abs_of_nonpos h0
  rw [hL, hR, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) (hcont.intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) (hcont.intervalIntegrable _ _)]
  have hFc : F c = 4 / 3 := by
    rw [hF, hc]; field_simp; ring
  have hFa : F a = 0 := by rw [hF]; simp
  have hFb : F (a + ℓ) = 1 := by rw [hF]; field_simp; ring
  rw [hFc, hFa, hFb]
  norm_num

/-- Integral de `|k_{a+ℓ}|` no intervalo: `∫_I |k_{a+ℓ}| = 5/3 ≤ 2` (mudança de sinal em `a+ℓ/3`). -/
theorem integral_abs_kR (a ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∫ y in Icc a (a + ℓ), |kR a ℓ y| = 5 / 3 := by
  set c : ℝ := a + ℓ / 3 with hc
  set G : ℝ → ℝ := fun y => (3 * (y - a) ^ 2 / ℓ - 2 * (y - a)) / ℓ with hG
  have hderiv : ∀ y, HasDerivAt G (kR a ℓ y) y := by
    intro y
    have h := ((((((hasDerivAt_id y).sub_const a).pow 2).const_mul (3 / ℓ)).sub
      (((hasDerivAt_id y).sub_const a).const_mul 2))).div_const ℓ
    convert h using 1
    all_goals first
      | (funext x; simp only [hG, id, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]; ring)
      | (unfold kR; simp only [id]; norm_num; field_simp; ring)
  have hcont : Continuous fun y => kR a ℓ y := by unfold kR; fun_prop
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hc1 : a ≤ c := by rw [hc]; nlinarith
  have hc2 : c ≤ a + ℓ := by rw [hc]; nlinarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := c) (c := a + ℓ)
    (hcont.abs.intervalIntegrable _ _) (hcont.abs.intervalIntegrable _ _)]
  have hL : ∫ y in a..c, |kR a ℓ y| = ∫ y in a..c, -kR a ℓ y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hc1] at hy
    have hq : (y - a) / ℓ ≤ 1 / 3 := by
      rw [div_le_iff₀ hℓ]
      have := hy.2
      rw [hc] at this
      linarith
    have h0 : kR a ℓ y ≤ 0 := by
      unfold kR
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hℓ.le
    simp only
    rw [abs_of_nonpos h0]
  have hR : ∫ y in c..a + ℓ, |kR a ℓ y| = ∫ y in c..a + ℓ, kR a ℓ y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hc2] at hy
    have hq : 1 / 3 ≤ (y - a) / ℓ := by
      rw [le_div_iff₀ hℓ]
      have := hy.1
      rw [hc] at this
      linarith
    have h0 : 0 ≤ kR a ℓ y := by
      unfold kR
      exact div_nonneg (by linarith) hℓ.le
    simp only
    exact abs_of_nonneg h0
  rw [hL, hR, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) (hcont.intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) (hcont.intervalIntegrable _ _)]
  have hGc : G c = -1 / 3 := by
    rw [hG, hc]; field_simp; ring
  have hGa : G a = 0 := by rw [hG]; simp
  have hGb : G (a + ℓ) = 1 := by rw [hG]; field_simp; ring
  rw [hGc, hGa, hGb]
  norm_num

/-- Cota pelo supremo: `|∫_I k_a g| ≤ 2M` se `|g| ≤ M` em `I` (usa `∫_I |k_a| = 5/3`). -/
theorem abs_integral_kL_mul_le {a ℓ M : ℝ} (hℓ : 0 < ℓ) (hM : 0 ≤ M) {g : ℝ → ℝ}
    (hgb : ∀ y ∈ Icc a (a + ℓ), |g y| ≤ M) :
    |∫ y in Icc a (a + ℓ), kL a ℓ y * g y| ≤ 2 * M := by
  have hcont : Continuous fun y => kL a ℓ y := by unfold kL; fun_prop
  have hint : Integrable (fun y => M * |kL a ℓ y|) (volume.restrict (Icc a (a + ℓ))) :=
    (hcont.abs.integrableOn_Icc).const_mul M
  have hae : ∀ᵐ y ∂(volume.restrict (Icc a (a + ℓ))), ‖kL a ℓ y * g y‖ ≤ M * |kL a ℓ y| := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hgb y hy) (abs_nonneg _)
  have h1 := norm_integral_le_of_norm_le hint hae
  rw [integral_const_mul, integral_abs_kL a ℓ hℓ, Real.norm_eq_abs] at h1
  linarith

/-- Cota pelo supremo, para o núcleo do extremo direito. -/
theorem abs_integral_kR_mul_le {a ℓ M : ℝ} (hℓ : 0 < ℓ) (hM : 0 ≤ M) {g : ℝ → ℝ}
    (hgb : ∀ y ∈ Icc a (a + ℓ), |g y| ≤ M) :
    |∫ y in Icc a (a + ℓ), kR a ℓ y * g y| ≤ 2 * M := by
  have hcont : Continuous fun y => kR a ℓ y := by unfold kR; fun_prop
  have hint : Integrable (fun y => M * |kR a ℓ y|) (volume.restrict (Icc a (a + ℓ))) :=
    (hcont.abs.integrableOn_Icc).const_mul M
  have hae : ∀ᵐ y ∂(volume.restrict (Icc a (a + ℓ))), ‖kR a ℓ y * g y‖ ≤ M * |kR a ℓ y| := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hgb y hy) (abs_nonneg _)
  have h1 := norm_integral_le_of_norm_le hint hae
  rw [integral_const_mul, integral_abs_kR a ℓ hℓ, Real.norm_eq_abs] at h1
  linarith

end FormalizacaoQuasi
