import Formalizacao.Whitney3

/-!
# Whitney em `L^p` (M5), parte 4: o erro `f - g` em `L^p`

Passo pontual: para cada `x`,
`|g(x) - f̃(x)|^p ≤ c · ∫_s ∫_r |W(x; s+r-δ)|^p`, com `c = (2δ²)^{-p} δ^{2(p-1)}`,
por Jensen duas vezes.
-/

open scoped ENNReal
open MeasureTheory Set intervalIntegral

namespace FormalizacaoW

variable {a b : ℝ} {f : ℝ → ℝ}

lemma ft_measurable (hfm : Measurable f) : Measurable (ft a b f) := by
  unfold ft
  exact hfm.indicator measurableSet_Icc

/-- `‖∫_0^δ φ‖ₑ ≤ ∫⁻_{Ioc 0 δ} ‖φ‖ₑ` -/
lemma enorm_intervalIntegral_le {δ : ℝ} (hδ : 0 ≤ δ) (φ : ℝ → ℝ) :
    ‖∫ s in (0 : ℝ)..δ, φ s‖ₑ ≤ ∫⁻ s in Ioc 0 δ, ‖φ s‖ₑ := by
  rw [intervalIntegral.integral_of_le hδ]
  exact enorm_integral_le_lintegral_enorm _

/-- **Passo pontual.** -/
theorem pointwise_fg {p : ℝ} (hp : 1 ≤ p) (hf : IntegrableOn f (Icc a b)) (hfm : Measurable f)
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ‖gs a b f δ x - ft a b f x‖ₑ ^ p ≤
      ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p * δ ^ (2 * (p - 1))) *
        ∫⁻ s in Ioc 0 δ, ∫⁻ r in Ioc 0 δ, ‖Wt (ft a b f) x (s + r - δ)‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hft := ft_measurable (a := a) (b := b) hfm
  set Θ : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..δ, Wt (ft a b f) x (s + r - δ) with hΘ
  have hmain : gs a b f δ x - ft a b f x = (1 / (2 * δ ^ 2)) * ∫ s in (0 : ℝ)..δ, Θ s := by
    have := double_sym hf hδ0 x
    rw [hΘ]
    simp only
    rw [this]
    field_simp
  -- Jensen em `s`
  have hΘc : Continuous Θ := by
    have cU := Uf_continuous hf
    have : Θ = fun s => (Uf a b f (x + s) - Uf a b f (x + s - δ)) +
        (Uf a b f (x - s + δ) - Uf a b f (x - s)) - 2 * δ * ft a b f x := by
      funext s; exact inner_Wt hf δ x s
    rw [this]
    fun_prop
  have hvolI : volume (Ioc 0 δ) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have J1 := jensen_set hp hvolI (φ := Θ) hΘc.measurable.aemeasurable
  have E1 : ‖∫ s in (0 : ℝ)..δ, Θ s‖ₑ ^ p ≤
      ENNReal.ofReal δ ^ (p - 1) * ∫⁻ s in Ioc 0 δ, ‖Θ s‖ₑ ^ p := by
    calc ‖∫ s in (0 : ℝ)..δ, Θ s‖ₑ ^ p ≤ (∫⁻ s in Ioc 0 δ, ‖Θ s‖ₑ) ^ p :=
          ENNReal.rpow_le_rpow (enorm_intervalIntegral_le hδ.le Θ) hp0.le
      _ ≤ _ := by rw [Real.volume_Ioc, sub_zero] at J1; exact J1
  -- Jensen em `r`, para cada `s`
  have E2 : ∀ s : ℝ, ‖Θ s‖ₑ ^ p ≤
      ENNReal.ofReal δ ^ (p - 1) * ∫⁻ r in Ioc 0 δ, ‖Wt (ft a b f) x (s + r - δ)‖ₑ ^ p := by
    intro s
    have hm : Measurable (fun r => Wt (ft a b f) x (s + r - δ)) := by
      unfold Wt; fun_prop
    have J2 := jensen_set hp hvolI (φ := fun r => Wt (ft a b f) x (s + r - δ)) hm.aemeasurable
    calc ‖Θ s‖ₑ ^ p ≤ (∫⁻ r in Ioc 0 δ, ‖Wt (ft a b f) x (s + r - δ)‖ₑ) ^ p :=
          ENNReal.rpow_le_rpow (enorm_intervalIntegral_le hδ.le _) hp0.le
      _ ≤ _ := by rw [Real.volume_Ioc, sub_zero] at J2; exact J2
  -- combinar
  rw [hmain, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  have hc : ‖(1 / (2 * δ ^ 2) : ℝ)‖ₑ ^ p = ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (by positivity), ENNReal.ofReal_rpow_of_nonneg
      (by positivity) hp0.le]
  rw [hc]
  have hne : ENNReal.ofReal δ ≠ 0 := by simpa using hδ
  have hnt : ENNReal.ofReal δ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hd : ENNReal.ofReal δ ^ (p - 1) * ENNReal.ofReal δ ^ (p - 1) =
      ENNReal.ofReal (δ ^ (2 * (p - 1))) := by
    calc ENNReal.ofReal δ ^ (p - 1) * ENNReal.ofReal δ ^ (p - 1)
        = ENNReal.ofReal δ ^ ((p - 1) + (p - 1)) := (ENNReal.rpow_add _ _ hne hnt).symm
      _ = ENNReal.ofReal (δ ^ ((p - 1) + (p - 1))) := ENNReal.ofReal_rpow_of_pos hδ
      _ = ENNReal.ofReal (δ ^ (2 * (p - 1))) := by congr 2; ring
  set X : ℝ≥0∞ := ∫⁻ s in Ioc 0 δ, ∫⁻ r in Ioc 0 δ, ‖Wt (ft a b f) x (s + r - δ)‖ₑ ^ p with hX
  have hmono : ∫⁻ s in Ioc 0 δ, ‖Θ s‖ₑ ^ p ≤
      ∫⁻ s in Ioc 0 δ, ENNReal.ofReal δ ^ (p - 1) *
        ∫⁻ r in Ioc 0 δ, ‖Wt (ft a b f) x (s + r - δ)‖ₑ ^ p :=
    setLIntegral_mono' measurableSet_Ioc (fun s _ => E2 s)
  have hpull : ∫⁻ s in Ioc 0 δ, ENNReal.ofReal δ ^ (p - 1) *
      ∫⁻ r in Ioc 0 δ, ‖Wt (ft a b f) x (s + r - δ)‖ₑ ^ p = ENNReal.ofReal δ ^ (p - 1) * X :=
    lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hnt)
  calc ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p) * ‖∫ s in (0 : ℝ)..δ, Θ s‖ₑ ^ p
      ≤ ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p) *
          (ENNReal.ofReal δ ^ (p - 1) * ∫⁻ s in Ioc 0 δ, ‖Θ s‖ₑ ^ p) :=
        mul_le_mul_left' E1 _
    _ ≤ ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p) *
          (ENNReal.ofReal δ ^ (p - 1) * (ENNReal.ofReal δ ^ (p - 1) * X)) := by
        rw [← hpull]
        exact mul_le_mul_left' (mul_le_mul_left' hmono _) _
    _ = ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p) *
          ((ENNReal.ofReal δ ^ (p - 1) * ENNReal.ofReal δ ^ (p - 1)) * X) := by ring
    _ = ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p) * (ENNReal.ofReal (δ ^ (2 * (p - 1))) * X) := by
        rw [hd]
    _ = ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p * δ ^ (2 * (p - 1))) * X := by
        rw [ENNReal.ofReal_mul (by positivity)]; ring

/-- integrando `‖W(x; s+r-δ)‖ₑ^p` -/
noncomputable def Fw (h : ℝ → ℝ) (δ p : ℝ) (x s r : ℝ) : ℝ≥0∞ := ‖Wt h x (s + r - δ)‖ₑ ^ p

lemma Fw_measurable {h : ℝ → ℝ} (hh : Measurable h) (δ p : ℝ) :
    Measurable (fun q : ℝ × ℝ × ℝ => Fw h δ p q.1 q.2.1 q.2.2) := by
  unfold Fw Wt
  have h1 : Measurable (fun q : ℝ × ℝ × ℝ => h (q.1 + (q.2.1 + q.2.2 - δ))) :=
    hh.comp (by fun_prop)
  have h2 : Measurable (fun q : ℝ × ℝ × ℝ => h (q.1 - (q.2.1 + q.2.2 - δ))) :=
    hh.comp (by fun_prop)
  have h3 : Measurable (fun q : ℝ × ℝ × ℝ => h q.1) := hh.comp (by fun_prop)
  have h4 : Measurable (fun q : ℝ × ℝ × ℝ =>
      h (q.1 + (q.2.1 + q.2.2 - δ)) + h (q.1 - (q.2.1 + q.2.2 - δ)) - 2 * h q.1) :=
    (h1.add h2).sub (h3.const_mul 2)
  have h5 := h4.enorm.pow_const p
  convert h5 using 2

lemma swap_xs {h : ℝ → ℝ} (hh : Measurable h) (δ p : ℝ) (S : Set ℝ) :
    ∫⁻ x in S, ∫⁻ s in Ioc 0 δ, ∫⁻ r in Ioc 0 δ, Fw h δ p x s r =
      ∫⁻ s in Ioc 0 δ, ∫⁻ x in S, ∫⁻ r in Ioc 0 δ, Fw h δ p x s r := by
  have hF := Fw_measurable hh δ p
  have h' : Measurable (fun q : (ℝ × ℝ) × ℝ => Fw h δ p q.1.1 q.1.2 q.2) :=
    hF.comp (by fun_prop : Measurable (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2, q.2)))
  refine lintegral_lintegral_swap ?_
  exact (h'.lintegral_prod_right' (ν := volume.restrict (Ioc 0 δ))).aemeasurable

lemma swap_xr {h : ℝ → ℝ} (hh : Measurable h) (δ p s : ℝ) (S : Set ℝ) :
    ∫⁻ x in S, ∫⁻ r in Ioc 0 δ, Fw h δ p x s r = ∫⁻ r in Ioc 0 δ, ∫⁻ x in S, Fw h δ p x s r := by
  have hF := Fw_measurable hh δ p
  have h' : Measurable (fun q : ℝ × ℝ => Fw h δ p q.1 s q.2) :=
    hF.comp (by fun_prop : Measurable (fun q : ℝ × ℝ => (q.1, s, q.2)))
  exact lintegral_lintegral_swap h'.aemeasurable

/-- **`f - g` em `L^p(S)`, com a integral em `x` no interior.** -/
theorem fg_lp {p : ℝ} (hp : 1 ≤ p) (hf : IntegrableOn f (Icc a b)) (hfm : Measurable f)
    {δ : ℝ} (hδ : 0 < δ) (S : Set ℝ) :
    ∫⁻ x in S, ‖gs a b f δ x - ft a b f x‖ₑ ^ p ≤
      ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p * δ ^ (2 * (p - 1))) *
        ∫⁻ s in Ioc 0 δ, ∫⁻ r in Ioc 0 δ, ∫⁻ x in S, Fw (ft a b f) δ p x s r := by
  have hft := ft_measurable (a := a) (b := b) hfm
  have step1 : ∫⁻ x in S, ‖gs a b f δ x - ft a b f x‖ₑ ^ p ≤
      ∫⁻ x in S, ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p * δ ^ (2 * (p - 1))) *
        ∫⁻ s in Ioc 0 δ, ∫⁻ r in Ioc 0 δ, Fw (ft a b f) δ p x s r :=
    lintegral_mono (fun x => pointwise_fg hp hf hfm hδ x)
  refine step1.trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, swap_xs hft δ p S]
  refine mul_le_mul_left' (le_of_eq ?_) _
  exact lintegral_congr (fun s => swap_xr hft δ p s S)

end FormalizacaoW
