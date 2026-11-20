import Formalizacao.Whitney6

/-!
# Whitney em `L^p` (M5), parte 7: o teorema local

Em `J = [a, a+8δ]`, existe uma reta `α + βx` tal que `∫_J |f - (α+βx)|^p` é limitado por
`K₁ · T + K₂ · c₀ · ∫_s ∫_r T(s+r-δ)`, onde `T(w) = ∫_I |W(x; w)|^p`, `I = [a+δ, a+7δ]`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoW

variable {a : ℝ} {f : ℝ → ℝ}

lemma gs_continuous (hf : IntegrableOn f (Icc a b)) (δ : ℝ) : Continuous (gs a b f δ) :=
  continuous_iff_continuousAt.2 (fun x => (gs_hasDerivAt hf δ x).continuousAt)

/-- **`f - g` em termos de `W f`.** -/
theorem fg_W {δ p : ℝ} (hp : 1 ≤ p) (hf : IntegrableOn f (Icc a (a + 8 * δ))) (hfm : Measurable f)
    (hδ : 0 < δ) :
    ∫⁻ x in Icc (a + δ) (a + 7 * δ), ‖gs a (a + 8 * δ) f δ x - ft a (a + 8 * δ) f x‖ₑ ^ p ≤
      ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p * δ ^ (2 * (p - 1))) *
        ∫⁻ s in Ioc 0 δ, ∫⁻ r in Ioc 0 δ, ∫⁻ x in Icc (a + δ) (a + 7 * δ), Fw f δ p x s r := by
  refine (fg_lp hp hf hfm hδ _).trans ?_
  refine mul_le_mul_left' (le_of_eq ?_) _
  refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
  refine setLIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
  have hw : |s + r - δ| ≤ δ := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, hr.1, hr.2]
  unfold Fw
  rw [Wt_ft_eq hx hw]

/-- constantes do teorema local (dependem só de `p`) -/
noncomputable def c4 (p : ℝ) : ℝ≥0∞ := 2 ^ (2 * (p - 1))
noncomputable def cM (p : ℝ) : ℝ≥0∞ := 1 + 2 * c4 p * (2 ^ p + 1)
noncomputable def cq (p : ℝ) : ℝ≥0∞ := 2 ^ (p - 1)
noncomputable def K2 (p : ℝ) : ℝ≥0∞ := cM p * cq p
noncomputable def K1 (p : ℝ) : ℝ≥0∞ := cM p * cq p * ENNReal.ofReal (6 ^ (2 * p)) + 2 * c4 p

lemma c4_ne_top {p : ℝ} (hp : 1 ≤ p) : c4 p ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg (by nlinarith) (by norm_num)
lemma cq_ne_top {p : ℝ} (hp : 1 ≤ p) : cq p ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
lemma cM_ne_top {p : ℝ} (hp : 1 ≤ p) : cM p ≠ ⊤ := by
  unfold cM
  have h2 : (2 : ℝ≥0∞) ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (c4_ne_top hp))
      (ENNReal.add_ne_top.2 ⟨h2, ENNReal.one_ne_top⟩)⟩
lemma K1_ne_top {p : ℝ} (hp : 1 ≤ p) : K1 p ≠ ⊤ := by
  unfold K1
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (cM_ne_top hp)
    (cq_ne_top hp)) ENNReal.ofReal_ne_top, ENNReal.mul_ne_top (by norm_num) (c4_ne_top hp)⟩
lemma K2_ne_top {p : ℝ} (hp : 1 ≤ p) : K2 p ≠ ⊤ :=
  ENNReal.mul_ne_top (cM_ne_top hp) (cq_ne_top hp)

/-- **Teorema local de Whitney em `L^p`.** Em `J = [a, a+8δ]` existe uma reta `α + βx` com
`∫_J |f - (α+βx)|^p ≤ K₁ ∫_I |W(·;δ)|^p + K₂ c₀ ∫_s ∫_r ∫_I |W(·; s+r-δ)|^p`. -/
theorem local_whitney {δ p : ℝ} (hp : 1 ≤ p) (hf : IntegrableOn f (Icc a (a + 8 * δ)))
    (hfm : Measurable f) (hδ : 0 < δ) :
    ∃ α β : ℝ, ∫⁻ x in Icc a (a + 8 * δ), ‖f x - (α + β * x)‖ₑ ^ p ≤
      K1 p * (∫⁻ x in Icc (a + δ) (a + 7 * δ), ‖Wt f x δ‖ₑ ^ p) +
      K2 p * (ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p * δ ^ (2 * (p - 1))) *
        ∫⁻ s in Ioc 0 δ, ∫⁻ r in Ioc 0 δ, ∫⁻ x in Icc (a + δ) (a + 7 * δ), Fw f δ p x s r) := by
  have hp0 : 0 < p := by linarith
  have hft := ft_measurable (a := a) (b := a + 8 * δ) hfm
  have hgm := (gs_continuous hf δ).measurable
  set β : ℝ := gs' a (a + 8 * δ) f δ (a + 4 * δ) with hβ
  set α : ℝ := gs a (a + 8 * δ) f δ (a + 4 * δ) - β * (a + 4 * δ) with hα
  refine ⟨α, β, ?_⟩
  set u : ℝ → ℝ := fun x => f x - (α + β * x) with hu
  set T : ℝ≥0∞ := ∫⁻ x in Icc (a + δ) (a + 7 * δ), ‖Wt f x δ‖ₑ ^ p with hT
  set X : ℝ≥0∞ := ∫⁻ x in Icc (a + δ) (a + 7 * δ), ‖u x‖ₑ ^ p with hX
  set Fint : ℝ≥0∞ := ∫⁻ s in Ioc 0 δ, ∫⁻ r in Ioc 0 δ, ∫⁻ x in Icc (a + δ) (a + 7 * δ),
    Fw f δ p x s r with hFint
  set c0 : ℝ≥0∞ := ENNReal.ofReal ((1 / (2 * δ ^ 2)) ^ p * δ ^ (2 * (p - 1))) with hc0
  have hum : Measurable u := hfm.sub (measurable_const.add (measurable_const.mul measurable_id))
  have hwm : Measurable (fun y => Wt f y δ) := by
    unfold Wt
    exact ((hfm.comp (by fun_prop)).add (hfm.comp (by fun_prop))).sub (hfm.const_mul 2)
  -- (1) parte interior
  have hTay := taylor_W hp hf hδ
  have hαβ : ∀ x, gs a (a + 8 * δ) f δ x - (gs a (a + 8 * δ) f δ (a + 4 * δ) +
      gs' a (a + 8 * δ) f δ (a + 4 * δ) * (x - (a + 4 * δ))) = gs a (a + 8 * δ) f δ x - (α + β * x) := by
    intro x; simp only [hα, hβ]; ring
  have hTay' : ∫⁻ x in Icc (a + δ) (a + 7 * δ), ‖gs a (a + 8 * δ) f δ x - (α + β * x)‖ₑ ^ p ≤
      ENNReal.ofReal (6 ^ (2 * p)) * T := by
    simp only [hαβ] at hTay
    exact hTay
  have hFg := fg_W hp hf hfm hδ
  have hXle : X ≤ cq p * (c0 * Fint + ENNReal.ofReal (6 ^ (2 * p)) * T) := by
    have pt : ∀ x ∈ Icc (a + δ) (a + 7 * δ), ‖u x‖ₑ ^ p ≤ cq p *
        (‖gs a (a + 8 * δ) f δ x - ft a (a + 8 * δ) f x‖ₑ ^ p +
          ‖gs a (a + 8 * δ) f δ x - (α + β * x)‖ₑ ^ p) := by
      intro x hx
      have hxJ : x ∈ Icc a (a + 8 * δ) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have e : u x = -(gs a (a + 8 * δ) f δ x - ft a (a + 8 * δ) f x) +
          (gs a (a + 8 * δ) f δ x - (α + β * x)) := by
        simp only [hu, ft_eq_of_mem hxJ]; ring
      have h1 : ‖u x‖ₑ ≤ ‖gs a (a + 8 * δ) f δ x - ft a (a + 8 * δ) f x‖ₑ +
          ‖gs a (a + 8 * δ) f δ x - (α + β * x)‖ₑ := by
        rw [e]
        calc _ ≤ ‖-(gs a (a + 8 * δ) f δ x - ft a (a + 8 * δ) f x)‖ₑ +
              ‖gs a (a + 8 * δ) f δ x - (α + β * x)‖ₑ := enorm_add_le _ _
          _ = _ := by rw [enorm_neg]
      calc ‖u x‖ₑ ^ p ≤ (‖gs a (a + 8 * δ) f δ x - ft a (a + 8 * δ) f x‖ₑ +
            ‖gs a (a + 8 * δ) f δ x - (α + β * x)‖ₑ) ^ p := ENNReal.rpow_le_rpow h1 hp0.le
        _ ≤ _ := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    have m1 : Measurable (fun x => ‖gs a (a + 8 * δ) f δ x - ft a (a + 8 * δ) f x‖ₑ ^ p) :=
      (hgm.sub hft).enorm.pow_const p
    calc X ≤ ∫⁻ x in Icc (a + δ) (a + 7 * δ), cq p *
          (‖gs a (a + 8 * δ) f δ x - ft a (a + 8 * δ) f x‖ₑ ^ p +
            ‖gs a (a + 8 * δ) f δ x - (α + β * x)‖ₑ ^ p) :=
          setLIntegral_mono' measurableSet_Icc pt
      _ = cq p * ((∫⁻ x in Icc (a + δ) (a + 7 * δ),
            ‖gs a (a + 8 * δ) f δ x - ft a (a + 8 * δ) f x‖ₑ ^ p) +
          (∫⁻ x in Icc (a + δ) (a + 7 * δ), ‖gs a (a + 8 * δ) f δ x - (α + β * x)‖ₑ ^ p)) := by
          rw [lintegral_const_mul' _ _ (cq_ne_top hp), lintegral_add_left m1]
      _ ≤ cq p * (c0 * Fint + ENNReal.ofReal (6 ^ (2 * p)) * T) := by
          gcongr
  -- (2) faixas laterais
  have hidL : ∀ x, u x = 2 * u (x + δ) - u (x + 2 * δ) + (fun y => Wt f y δ) (x + δ) := by
    intro x
    have e1 : x + δ + δ = x + 2 * δ := by ring
    have e2 : x + δ - δ = x := by ring
    simp only [hu, Wt, e1, e2]; ring
  have hidR : ∀ x, u x = 2 * u (x - δ) - u (x - 2 * δ) + (fun y => Wt f y δ) (x - δ) := by
    intro x
    have e1 : x - δ + δ = x := by ring
    have e2 : x - δ - δ = x - 2 * δ := by ring
    simp only [hu, Wt, e1, e2]; ring
  have hL := strip_left hp hum hwm a hidL
  have hR := strip_right hp hum hwm (a + 8 * δ) hidR
  have mono_u : ∀ {s : Set ℝ}, s ⊆ Icc (a + δ) (a + 7 * δ) →
      ∫⁻ y in s, ‖u y‖ₑ ^ p ≤ X := fun hs => lintegral_mono_set hs
  have mono_w : ∀ {s : Set ℝ}, s ⊆ Icc (a + δ) (a + 7 * δ) →
      ∫⁻ y in s, ‖Wt f y δ‖ₑ ^ p ≤ T := fun hs => lintegral_mono_set hs
  have hL' : ∫⁻ x in Icc a (a + δ), ‖u x‖ₑ ^ p ≤ c4 p * (2 ^ p * X + X + T) := by
    refine hL.trans ?_
    unfold c4
    gcongr
    · exact mono_u (Icc_subset_Icc le_rfl (by linarith))
    · exact mono_u (Icc_subset_Icc (by linarith) (by linarith))
    · exact mono_w (Icc_subset_Icc le_rfl (by linarith))
  have hR' : ∫⁻ x in Icc (a + 8 * δ - δ) (a + 8 * δ), ‖u x‖ₑ ^ p ≤ c4 p * (2 ^ p * X + X + T) := by
    refine hR.trans ?_
    unfold c4
    gcongr
    · exact mono_u (Icc_subset_Icc (by linarith) (by linarith))
    · exact mono_u (Icc_subset_Icc (by linarith) (by linarith))
    · exact mono_w (Icc_subset_Icc (by linarith) (by linarith))
  -- (3) união
  have hsub : Icc a (a + 8 * δ) ⊆ Icc a (a + δ) ∪ Icc (a + δ) (a + 7 * δ) ∪
      Icc (a + 8 * δ - δ) (a + 8 * δ) := by
    intro x hx
    by_cases h1 : x ≤ a + δ
    · exact Or.inl (Or.inl ⟨hx.1, h1⟩)
    · by_cases h2 : x ≤ a + 7 * δ
      · exact Or.inl (Or.inr ⟨by linarith, h2⟩)
      · exact Or.inr ⟨by linarith, hx.2⟩
  calc ∫⁻ x in Icc a (a + 8 * δ), ‖f x - (α + β * x)‖ₑ ^ p
      ≤ ∫⁻ x in Icc a (a + δ) ∪ Icc (a + δ) (a + 7 * δ) ∪ Icc (a + 8 * δ - δ) (a + 8 * δ),
          ‖u x‖ₑ ^ p := lintegral_mono_set hsub
    _ ≤ (∫⁻ x in Icc a (a + δ) ∪ Icc (a + δ) (a + 7 * δ), ‖u x‖ₑ ^ p) +
          ∫⁻ x in Icc (a + 8 * δ - δ) (a + 8 * δ), ‖u x‖ₑ ^ p := lintegral_union_le _ _ _
    _ ≤ ((∫⁻ x in Icc a (a + δ), ‖u x‖ₑ ^ p) + X) +
          ∫⁻ x in Icc (a + 8 * δ - δ) (a + 8 * δ), ‖u x‖ₑ ^ p := by
        gcongr; exact lintegral_union_le _ _ _
    _ ≤ (c4 p * (2 ^ p * X + X + T) + X) + c4 p * (2 ^ p * X + X + T) := by
        gcongr
    _ = cM p * X + 2 * c4 p * T := by unfold cM; ring
    _ ≤ cM p * (cq p * (c0 * Fint + ENNReal.ofReal (6 ^ (2 * p)) * T)) + 2 * c4 p * T := by
        gcongr
    _ = K1 p * T + K2 p * (c0 * Fint) := by unfold K1 K2; ring

end FormalizacaoW
