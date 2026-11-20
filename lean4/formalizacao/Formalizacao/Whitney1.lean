import Formalizacao.Whitney0

/-!
# Whitney em `L^p` (M5), parte 1: suavização por média dupla e fórmula de Taylor

Para `f` integrável em `[a,b]`, ponha `f̃ = 1_{[a,b]} f` (integrável em `ℝ`),
`U(y) = ∫_a^y f̃` e `V(y) = ∫_a^y U`. A suavização é
`g(x) = δ⁻² (V(x+δ) - 2V(x) + V(x-δ))`. `V' = U` é contínua, logo `g` é `C¹` com
`g'(x) = δ⁻²(U(x+δ) - 2U(x) + U(x-δ))`, e
`g'(t) - g'(c) = ∫_c^t G`, `G(r) = δ⁻²(f̃(r+δ) - 2 f̃(r) + f̃(r-δ))`.
-/

open scoped ENNReal
open MeasureTheory Set intervalIntegral

namespace FormalizacaoW

section Smooth

variable (a b : ℝ) (f : ℝ → ℝ)

/-- `f` restrita a `[a,b]` e nula fora. -/
noncomputable def ft : ℝ → ℝ := (Icc a b).indicator f

/-- primitiva `U(y) = ∫_a^y f̃`. -/
noncomputable def Uf (y : ℝ) : ℝ := ∫ t in a..y, ft a b f t

/-- primitiva dupla `V(y) = ∫_a^y U`. -/
noncomputable def Vf (y : ℝ) : ℝ := ∫ t in a..y, Uf a b f t

/-- suavização `g(x) = δ⁻² (V(x+δ) - 2V(x) + V(x-δ))`. -/
noncomputable def gs (δ x : ℝ) : ℝ := (Vf a b f (x + δ) - 2 * Vf a b f x + Vf a b f (x - δ)) / δ ^ 2

/-- derivada de `g`: `g'(x) = δ⁻²(U(x+δ) - 2U(x) + U(x-δ))`. -/
noncomputable def gs' (δ x : ℝ) : ℝ := (Uf a b f (x + δ) - 2 * Uf a b f x + Uf a b f (x - δ)) / δ ^ 2

/-- `G(r) = δ⁻²(f̃(r+δ) - 2 f̃(r) + f̃(r-δ))`. -/
noncomputable def Gs (δ r : ℝ) : ℝ := (ft a b f (r + δ) - 2 * ft a b f r + ft a b f (r - δ)) / δ ^ 2

variable {a b f}

lemma ft_integrable (hf : IntegrableOn f (Icc a b)) : Integrable (ft a b f) := by
  unfold ft
  exact (integrable_indicator_iff measurableSet_Icc).2 hf

lemma ft_intervalIntegrable (hf : IntegrableOn f (Icc a b)) (u v : ℝ) :
    IntervalIntegrable (ft a b f) volume u v :=
  (ft_integrable hf).intervalIntegrable

lemma Uf_continuous (hf : IntegrableOn f (Icc a b)) : Continuous (Uf a b f) := by
  unfold Uf
  exact intervalIntegral.continuous_primitive (fun u v => ft_intervalIntegrable hf u v) a

lemma Vf_hasDerivAt (hf : IntegrableOn f (Icc a b)) (y : ℝ) :
    HasDerivAt (Vf a b f) (Uf a b f y) y := by
  unfold Vf
  have hc := Uf_continuous hf
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a y)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

lemma gs_hasDerivAt (hf : IntegrableOn f (Icc a b)) (δ x : ℝ) :
    HasDerivAt (gs a b f δ) (gs' a b f δ x) x := by
  have h1 := (Vf_hasDerivAt hf (x + δ)).comp_add_const x δ
  have h2 := Vf_hasDerivAt hf x
  have h3 := (Vf_hasDerivAt hf (x - δ)).comp_sub_const x δ
  have h4 := ((h1.sub (h2.const_mul 2)).add h3)
  have h5 := h4.div_const (δ ^ 2)
  unfold gs gs'
  convert h5 using 1

lemma Uf_sub (hf : IntegrableOn f (Icc a b)) (y z : ℝ) :
    Uf a b f y - Uf a b f z = ∫ t in z..y, ft a b f t := by
  unfold Uf
  exact intervalIntegral.integral_interval_sub_left (ft_intervalIntegrable hf a y)
    (ft_intervalIntegrable hf a z)

lemma gs'_continuous (hf : IntegrableOn f (Icc a b)) (δ : ℝ) : Continuous (gs' a b f δ) := by
  have hU := Uf_continuous hf
  unfold gs'
  fun_prop

/-- `g'(t) - g'(c) = ∫_c^t G`. -/
lemma gs'_sub (hf : IntegrableOn f (Icc a b)) (δ c t : ℝ) :
    gs' a b f δ t - gs' a b f δ c = ∫ r in c..t, Gs a b f δ r := by
  have hI := ft_intervalIntegrable hf
  have e1 : Uf a b f (t + δ) - Uf a b f (c + δ) = ∫ r in c..t, ft a b f (r + δ) := by
    rw [Uf_sub hf, intervalIntegral.integral_comp_add_right]
  have e2 : Uf a b f t - Uf a b f c = ∫ r in c..t, ft a b f r := Uf_sub hf t c
  have e3 : Uf a b f (t - δ) - Uf a b f (c - δ) = ∫ r in c..t, ft a b f (r - δ) := by
    rw [Uf_sub hf, intervalIntegral.integral_comp_sub_right]
  have i1 : IntervalIntegrable (fun r => ft a b f (r + δ)) volume c t := by
    have := (hI (c + δ) (t + δ)).comp_add_right δ
    simpa using this
  have i2 : IntervalIntegrable (fun r => ft a b f r) volume c t := hI c t
  have i3 : IntervalIntegrable (fun r => ft a b f (r - δ)) volume c t := by
    have := (hI (c - δ) (t - δ)).comp_sub_right δ
    simpa using this
  have key : gs' a b f δ t - gs' a b f δ c =
      ((Uf a b f (t + δ) - Uf a b f (c + δ)) - 2 * (Uf a b f t - Uf a b f c)
        + (Uf a b f (t - δ) - Uf a b f (c - δ))) / δ ^ 2 := by
    unfold gs'; ring
  rw [key, e1, e2, e3]
  simp only [Gs]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (i1.sub (i2.const_mul 2)) i3,
    intervalIntegral.integral_sub i1 (i2.const_mul 2), intervalIntegral.integral_const_mul]

/-- Fórmula de Taylor com resto integral:
`g(x) - g(c) - g'(c)(x-c) = ∫_c^x (g'(t) - g'(c)) dt`. -/
lemma gs_taylor (hf : IntegrableOn f (Icc a b)) (δ c x : ℝ) :
    gs a b f δ x - gs a b f δ c - gs' a b f δ c * (x - c) =
      ∫ t in c..x, (gs' a b f δ t - gs' a b f δ c) := by
  have h1 : ∫ t in c..x, gs' a b f δ t = gs a b f δ x - gs a b f δ c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => gs_hasDerivAt hf δ t)
      ((gs'_continuous hf δ).intervalIntegrable c x)
  rw [intervalIntegral.integral_sub ((gs'_continuous hf δ).intervalIntegrable c x)
    _root_.intervalIntegrable_const, h1, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma abs_integral_le_of_le {G : ℝ → ℝ} {lo hi c t : ℝ} (hG : IntervalIntegrable G volume lo hi)
    (hc : lo ≤ c) (hct : c ≤ t) (ht : t ≤ hi) :
    |∫ r in c..t, G r| ≤ ∫ r in lo..hi, |G r| := by
  have hlo : IntervalIntegrable G volume lo c := hG.mono_set (by
    rw [uIcc_of_le (hc.trans (hct.trans ht)), uIcc_of_le hc]
    exact Icc_subset_Icc le_rfl (hct.trans ht))
  have hct' : IntervalIntegrable G volume c t := hG.mono_set (by
    rw [uIcc_of_le (hc.trans (hct.trans ht)), uIcc_of_le hct]
    exact Icc_subset_Icc hc ht)
  have hth : IntervalIntegrable G volume t hi := hG.mono_set (by
    rw [uIcc_of_le (hc.trans (hct.trans ht)), uIcc_of_le ht]
    exact Icc_subset_Icc (hc.trans hct) le_rfl)
  calc |∫ r in c..t, G r| ≤ ∫ r in c..t, |G r| :=
        intervalIntegral.abs_integral_le_integral_abs hct
    _ ≤ (∫ r in lo..c, |G r|) + (∫ r in c..t, |G r|) + (∫ r in t..hi, |G r|) := by
        have h1 : 0 ≤ ∫ r in lo..c, |G r| := intervalIntegral.integral_nonneg hc (fun _ _ => abs_nonneg _)
        have h2 : 0 ≤ ∫ r in t..hi, |G r| := intervalIntegral.integral_nonneg ht (fun _ _ => abs_nonneg _)
        linarith
    _ = ∫ r in lo..hi, |G r| := by
        rw [intervalIntegral.integral_add_adjacent_intervals hlo.abs hct'.abs,
          intervalIntegral.integral_add_adjacent_intervals (hlo.trans hct').abs hth.abs]

lemma Gs_integrable (hf : IntegrableOn f (Icc a b)) (δ : ℝ) : Integrable (Gs a b f δ) := by
  have h := ft_integrable hf
  unfold Gs
  refine Integrable.div_const ?_ _
  exact ((h.comp_add_right δ).sub ((h.const_mul 2))).add (h.comp_sub_right δ) |>.congr
    (Filter.Eventually.of_forall fun r => by simp [sub_eq_add_neg, add_assoc, mul_comm])

lemma abs_integral_le_of_mem {G : ℝ → ℝ} {lo hi c t : ℝ} (hG : IntervalIntegrable G volume lo hi)
    (hc : c ∈ Icc lo hi) (ht : t ∈ Icc lo hi) :
    |∫ r in c..t, G r| ≤ ∫ r in lo..hi, |G r| := by
  rcases le_total c t with h | h
  · exact abs_integral_le_of_le hG hc.1 h ht.2
  · rw [intervalIntegral.integral_symm, abs_neg]
    exact abs_integral_le_of_le hG ht.1 h hc.2

/-- **Cota pontual do resto de Taylor.** Para `c, x ∈ [lo, hi]`:
`|g(x) - g(c) - g'(c)(x-c)| ≤ |x-c| · ∫_lo^hi |G|`. -/
lemma gs_taylor_bound (hf : IntegrableOn f (Icc a b)) (δ : ℝ) {lo hi c x : ℝ} (hlo : lo ≤ hi)
    (hc : c ∈ Icc lo hi) (hx : x ∈ Icc lo hi) :
    |gs a b f δ x - gs a b f δ c - gs' a b f δ c * (x - c)| ≤
      |x - c| * ∫ r in lo..hi, |Gs a b f δ r| := by
  have hGi : IntervalIntegrable (Gs a b f δ) volume lo hi := (Gs_integrable hf δ).intervalIntegrable
  rw [gs_taylor hf δ c x]
  have hb : ‖∫ t in c..x, (gs' a b f δ t - gs' a b f δ c)‖ ≤
      (∫ r in lo..hi, |Gs a b f δ r|) * |x - c| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => ?_)
    have htmem : t ∈ Icc lo hi := by
      have : Set.uIoc c x ⊆ Icc lo hi := by
        rw [Set.uIoc]
        intro y hy
        rcases le_total c x with h | h
        · rw [min_eq_left h, max_eq_right h] at hy
          exact ⟨hc.1.trans hy.1.le, hy.2.trans hx.2⟩
        · rw [min_eq_right h, max_eq_left h] at hy
          exact ⟨hx.1.trans hy.1.le, hy.2.trans hc.2⟩
      exact this ht
    rw [gs'_sub hf δ c t, Real.norm_eq_abs]
    exact abs_integral_le_of_mem hGi hc htmem
  rw [Real.norm_eq_abs] at hb
  rw [mul_comm]
  exact hb

end Smooth

end FormalizacaoW
