import Formalizacao.Whitney2

/-!
# Whitney em `L^p` (M5), parte 3: simetrização

`W(x; w) = h(x+w) + h(x-w) - 2h(x)` é a segunda diferença centrada (par em `w`). Mostra-se
`∫_0^δ ∫_0^δ W(x; s+r-δ) dr ds = 2 δ² (g(x) - f̃(x))`.
-/

open scoped ENNReal
open MeasureTheory Set intervalIntegral

namespace FormalizacaoW

/-- segunda diferença centrada `W(x; w) = h(x+w) + h(x-w) - 2h(x)` -/
def Wt (h : ℝ → ℝ) (x w : ℝ) : ℝ := h (x + w) + h (x - w) - 2 * h x

variable {a b : ℝ} {f : ℝ → ℝ}

lemma Vf_sub (hf : IntegrableOn f (Icc a b)) (y z : ℝ) :
    Vf a b f y - Vf a b f z = ∫ t in z..y, Uf a b f t := by
  unfold Vf
  exact intervalIntegral.integral_interval_sub_left
    ((Uf_continuous hf).intervalIntegrable a y) ((Uf_continuous hf).intervalIntegrable a z)

lemma int_Uf_add (hf : IntegrableOn f (Icc a b)) (c δ : ℝ) :
    ∫ s in (0 : ℝ)..δ, Uf a b f (c + s) = Vf a b f (c + δ) - Vf a b f c := by
  rw [intervalIntegral.integral_comp_add_left (fun t => Uf a b f t), Vf_sub hf]
  simp

lemma int_Uf_sub (hf : IntegrableOn f (Icc a b)) (c δ : ℝ) :
    ∫ s in (0 : ℝ)..δ, Uf a b f (c - s) = Vf a b f c - Vf a b f (c - δ) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t => Uf a b f t), Vf_sub hf]
  simp

lemma int_ft_add (hf : IntegrableOn f (Icc a b)) (c δ : ℝ) :
    ∫ r in (0 : ℝ)..δ, ft a b f (c + r) = Uf a b f (c + δ) - Uf a b f c := by
  rw [intervalIntegral.integral_comp_add_left (fun t => ft a b f t), Uf_sub hf]
  simp

lemma int_ft_sub (hf : IntegrableOn f (Icc a b)) (c δ : ℝ) :
    ∫ r in (0 : ℝ)..δ, ft a b f (c - r) = Uf a b f c - Uf a b f (c - δ) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t => ft a b f t), Uf_sub hf]
  simp

/-- integral interno em forma fechada -/
lemma inner_Wt (hf : IntegrableOn f (Icc a b)) (δ x s : ℝ) :
    ∫ r in (0 : ℝ)..δ, Wt (ft a b f) x (s + r - δ) =
      (Uf a b f (x + s) - Uf a b f (x + s - δ)) + (Uf a b f (x - s + δ) - Uf a b f (x - s))
        - 2 * δ * ft a b f x := by
  have hI := ft_intervalIntegrable hf
  have i1 : IntervalIntegrable (fun r => ft a b f (x + (s - δ) + r)) volume 0 δ := by
    have := (hI (x + (s - δ) + 0) (x + (s - δ) + δ)).comp_add_left (x + (s - δ))
    simpa [add_assoc] using this
  have i2 : IntervalIntegrable (fun r => ft a b f ((x - s + δ) - r)) volume 0 δ := by
    have := (hI ((x - s + δ) - δ) ((x - s + δ) - 0)).comp_sub_left (x - s + δ)
    simpa using this.symm
  have e1 : ∀ r : ℝ, Wt (ft a b f) x (s + r - δ) =
      ft a b f (x + (s - δ) + r) + ft a b f ((x - s + δ) - r) - 2 * ft a b f x := by
    intro r; unfold Wt; ring_nf
  simp_rw [e1]
  rw [intervalIntegral.integral_sub (i1.add i2) (_root_.intervalIntegrable_const),
    intervalIntegral.integral_add i1 i2, int_ft_add hf, int_ft_sub hf]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have h1 : x + (s - δ) + δ = x + s := by ring
  have h2 : x + (s - δ) = x + s - δ := by ring
  have h3 : x - s + δ - δ = x - s := by ring
  rw [h1, h2, h3]
  ring

/-- **Identidade de simetrização.**
`∫_0^δ ∫_0^δ W(x; s+r-δ) dr ds = 2 δ² (g(x) - f̃(x))`. -/
theorem double_sym (hf : IntegrableOn f (Icc a b)) {δ : ℝ} (hδ : δ ≠ 0) (x : ℝ) :
    ∫ s in (0 : ℝ)..δ, ∫ r in (0 : ℝ)..δ, Wt (ft a b f) x (s + r - δ) =
      2 * δ ^ 2 * (gs a b f δ x - ft a b f x) := by
  have cU := Uf_continuous hf
  have ia : IntervalIntegrable (fun s => Uf a b f (x + s)) volume 0 δ :=
    (cU.comp (by fun_prop : Continuous fun s : ℝ => x + s)).intervalIntegrable 0 δ
  have ib : IntervalIntegrable (fun s => Uf a b f (x + s - δ)) volume 0 δ :=
    (cU.comp (by fun_prop : Continuous fun s : ℝ => x + s - δ)).intervalIntegrable 0 δ
  have ic : IntervalIntegrable (fun s => Uf a b f (x - s + δ)) volume 0 δ :=
    (cU.comp (by fun_prop : Continuous fun s : ℝ => x - s + δ)).intervalIntegrable 0 δ
  have id' : IntervalIntegrable (fun s => Uf a b f (x - s)) volume 0 δ :=
    (cU.comp (by fun_prop : Continuous fun s : ℝ => x - s)).intervalIntegrable 0 δ
  simp_rw [inner_Wt hf]
  rw [intervalIntegral.integral_sub ((ia.sub ib).add (ic.sub id')) _root_.intervalIntegrable_const,
    intervalIntegral.integral_add (ia.sub ib) (ic.sub id'), intervalIntegral.integral_sub ia ib,
    intervalIntegral.integral_sub ic id']
  have e1 : ∫ s in (0 : ℝ)..δ, Uf a b f (x + s) = Vf a b f (x + δ) - Vf a b f x := int_Uf_add hf x δ
  have e2 : ∫ s in (0 : ℝ)..δ, Uf a b f (x + s - δ) = Vf a b f x - Vf a b f (x - δ) := by
    have := int_Uf_add hf (x - δ) δ
    simp only [sub_add_cancel] at this
    rw [← this]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    show Uf a b f _ = Uf a b f _
    congr 1; ring
  have e3 : ∫ s in (0 : ℝ)..δ, Uf a b f (x - s + δ) = Vf a b f (x + δ) - Vf a b f x := by
    have := int_Uf_sub hf (x + δ) δ
    simp only [add_sub_cancel_right] at this
    rw [← this]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    show Uf a b f _ = Uf a b f _
    congr 1; ring
  have e4 : ∫ s in (0 : ℝ)..δ, Uf a b f (x - s) = Vf a b f x - Vf a b f (x - δ) := by
    have := int_Uf_sub hf x δ
    exact this
  rw [e1, e2, e3, e4]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  unfold gs
  field_simp
  ring

end FormalizacaoW
