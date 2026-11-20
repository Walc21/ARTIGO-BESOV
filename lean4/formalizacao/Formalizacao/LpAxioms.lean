import Formalizacao.LpDefs

/-!
# Axiomas do módulo em `L^p` (M2 do plano de formalização)

Prova, para `ω_p = wtP p` e `distP p`, os análogos em `ENNReal` dos três axiomas do
arcabouço abstrato (`Formalizacao.Modulo`):

* subaditividade `ω_p(f+g,t) ≤ ω_p(f,t) + ω_p(g,t)` (`wtP_add_le`);
* cota `ω_p(g,t) ≤ 4‖g‖_{L^p([0,1])}` (`wtP_le_four`);
* monotonia em `t` (`wtP_mono_t`);

e a desigualdade inversa `ω_p(f, 1/N) ≤ 4 R_N^G(f)_p` (`wtP_le_four_realP`),
que é a Proposição `lp:prop:inverse` em `L^p`.

Hipótese: as funções são mensuráveis e `1 ≤ p`. Para a família `G`, pede-se que
seus elementos sejam mensuráveis (`Σ_N` da Parte IV consiste de funções contínuas).
-/

open MeasureTheory Set ENNReal

namespace FormalizacaoLp

lemma diff2_add (h : ℝ) (f g : ℝ → ℝ) : diff2 h (f + g) = diff2 h f + diff2 h g := by
  funext x
  simp only [diff2, Pi.add_apply]
  ring

lemma measurable_diff2 {f : ℝ → ℝ} (hf : Measurable f) (h : ℝ) : Measurable (diff2 h f) := by
  unfold diff2
  have h1 : Measurable fun x : ℝ => f (x + 2 * h) := hf.comp (measurable_id.add_const _)
  have h2 : Measurable fun x : ℝ => f (x + h) := hf.comp (measurable_id.add_const _)
  exact (h1.sub (measurable_const.mul h2)).add hf

/-- Cada parcela da supremo em `wtP` é limitada pelo supremo. -/
lemma le_wtP (p : ℝ≥0∞) (t : ℝ) (f : ℝ → ℝ) {h : ℝ} (hh : h ∈ Ioc 0 (min t (1 / 2))) :
    eLpNorm (diff2 h f) p (volume.restrict (Icc 0 (1 - 2 * h))) ≤ wtP p t f :=
  le_iSup₂ (f := fun (h : ℝ) (_ : h ∈ Ioc 0 (min t (1 / 2))) =>
    eLpNorm (diff2 h f) p (volume.restrict (Icc 0 (1 - 2 * h)))) h hh

/-- Subaditividade de `ω_p` (axioma (a) do arcabouço). -/
theorem wtP_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (t : ℝ) {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    wtP p t (f + g) ≤ wtP p t f + wtP p t g := by
  unfold wtP
  refine iSup₂_le fun h hh => ?_
  rw [diff2_add]
  refine (eLpNorm_add_le (measurable_diff2 hf h).aestronglyMeasurable
    (measurable_diff2 hg h).aestronglyMeasurable hp).trans ?_
  exact add_le_add (le_wtP p t f hh) (le_wtP p t g hh)

/-- Monotonia de `ω_p` em `t` (axioma (c) do arcabouço). -/
theorem wtP_mono_t (p : ℝ≥0∞) (f : ℝ → ℝ) {s t : ℝ} (hst : s ≤ t) :
    wtP p s f ≤ wtP p t f := by
  unfold wtP
  refine iSup₂_le fun h hh => ?_
  exact le_iSup₂_of_le h ⟨hh.1, le_trans hh.2 (min_le_min_right _ hst)⟩ le_rfl

/-- `‖ 1_{[0,1]}(y) ‖g(y)‖ ‖` tem a mesma norma `L^p` que `g` em `[0,1]`. -/
lemma eLpNorm_indicator_norm (p : ℝ≥0∞) (g : ℝ → ℝ) :
    eLpNorm ((Icc (0 : ℝ) 1).indicator fun y => ‖g y‖) p volume = eLpNorm g p vol01 := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc, eLpNorm_norm]

/-- Invariância por translação da norma `L^p` em `ℝ` (medida de Lebesgue). -/
lemma eLpNorm_translate (p : ℝ≥0∞) {G : ℝ → ℝ} (hG : Measurable G) (c : ℝ) :
    eLpNorm (fun x => G (x + c)) p volume = eLpNorm G p volume := by
  have hm : MeasurePreserving (fun x : ℝ => x + c) volume volume :=
    measurePreserving_add_right volume c
  exact eLpNorm_comp_measurePreserving hG.aestronglyMeasurable hm

/-- Majorante `G_g(y) = 1_{[0,1]}(y) ‖g(y)‖`. -/
noncomputable def Gbound (g : ℝ → ℝ) : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator fun y => ‖g y‖

lemma Gbound_nonneg (g : ℝ → ℝ) (y : ℝ) : 0 ≤ Gbound g y :=
  indicator_nonneg (fun y _ => norm_nonneg _) y

lemma Gbound_measurable {g : ℝ → ℝ} (hg : Measurable g) : Measurable (Gbound g) :=
  hg.norm.indicator measurableSet_Icc

/-- Ponto a ponto: a segunda diferença restrita a `[0,1-2h]` é majorada por `G`. -/
lemma pt_bound {g : ℝ → ℝ} {h : ℝ} (hpos : 0 < h) (x : ℝ) :
    ‖(Icc (0 : ℝ) (1 - 2 * h)).indicator (diff2 h g) x‖ ≤
      Gbound g (x + 2 * h) + 2 * Gbound g (x + h) + Gbound g x := by
  by_cases hx : x ∈ Icc (0 : ℝ) (1 - 2 * h)
  · rw [indicator_of_mem hx]
    have h1 : x + 2 * h ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h2 : x + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h3 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
    have e1 : Gbound g (x + 2 * h) = ‖g (x + 2 * h)‖ := indicator_of_mem h1 _
    have e2 : Gbound g (x + h) = ‖g (x + h)‖ := indicator_of_mem h2 _
    have e3 : Gbound g x = ‖g x‖ := indicator_of_mem h3 _
    rw [e1, e2, e3]
    unfold diff2
    have t1 := norm_sub_le (g (x + 2 * h)) (2 * g (x + h))
    have t2 := norm_add_le (g (x + 2 * h) - 2 * g (x + h)) (g x)
    have t3 : ‖2 * g (x + h)‖ = 2 * ‖g (x + h)‖ := by
      rw [norm_mul]; norm_num
    linarith
  · rw [indicator_of_notMem hx, norm_zero]
    have := Gbound_nonneg g (x + 2 * h)
    have := Gbound_nonneg g (x + h)
    have := Gbound_nonneg g x
    linarith

/-- Parte 1 da estimativa: a soma de três translações de `G` tem norma `≤ 4 ‖G‖`. -/
lemma eLpNorm_three_terms {p : ℝ≥0∞} (hp : 1 ≤ p) {G : ℝ → ℝ} (hG : Measurable G) (h : ℝ) :
    eLpNorm (fun x : ℝ => G (x + 2 * h) + 2 * G (x + h) + G x) p volume ≤
      4 * eLpNorm G p volume := by
  have hm1 : Measurable fun x : ℝ => G (x + 2 * h) := hG.comp (measurable_id.add_const _)
  have hm2 : Measurable fun x : ℝ => G (x + h) := hG.comp (measurable_id.add_const _)
  have hm3 : Measurable fun x : ℝ => 2 * G (x + h) := measurable_const.mul hm2
  have hsc : (fun x : ℝ => 2 * G (x + h)) = (2 : ℝ) • (fun x : ℝ => G (x + h)) := by
    funext x; simp [Pi.smul_apply, smul_eq_mul]
  have hA : eLpNorm (fun x : ℝ => G (x + 2 * h) + 2 * G (x + h)) p volume ≤
      eLpNorm (fun x : ℝ => G (x + 2 * h)) p volume +
        eLpNorm (fun x : ℝ => 2 * G (x + h)) p volume :=
    eLpNorm_add_le (μ := volume) hm1.aestronglyMeasurable hm3.aestronglyMeasurable hp
  have hB : eLpNorm (fun x : ℝ => G (x + 2 * h) + 2 * G (x + h) + G x) p volume ≤
      eLpNorm (fun x : ℝ => G (x + 2 * h) + 2 * G (x + h)) p volume + eLpNorm G p volume := by
    exact eLpNorm_add_le (μ := volume) (hm1.add hm3).aestronglyMeasurable
      hG.aestronglyMeasurable hp
  have hT1 : eLpNorm (fun x : ℝ => G (x + 2 * h)) p volume = eLpNorm G p volume :=
    eLpNorm_translate p hG (2 * h)
  have hT2 : eLpNorm (fun x : ℝ => 2 * G (x + h)) p volume = 2 * eLpNorm G p volume := by
    rw [hsc, eLpNorm_const_smul, eLpNorm_translate p hG h]
    have h2 : ‖(2 : ℝ)‖ₑ = 2 := by rw [Real.enorm_eq_ofReal zero_le_two]; simp
    rw [h2]
  have hsum : eLpNorm G p volume + 2 * eLpNorm G p volume + eLpNorm G p volume =
      4 * eLpNorm G p volume := by ring
  calc eLpNorm (fun x : ℝ => G (x + 2 * h) + 2 * G (x + h) + G x) p volume
      ≤ eLpNorm (fun x : ℝ => G (x + 2 * h) + 2 * G (x + h)) p volume + eLpNorm G p volume := hB
    _ ≤ (eLpNorm (fun x : ℝ => G (x + 2 * h)) p volume +
          eLpNorm (fun x : ℝ => 2 * G (x + h)) p volume) + eLpNorm G p volume :=
        add_le_add hA le_rfl
    _ = 4 * eLpNorm G p volume := by rw [hT1, hT2, ← hsum]

/-- Estimativa integral: `‖Δ²_h g‖_{L^p([0,1-2h])} ≤ 4 ‖g‖_{L^p([0,1])}`. -/
lemma eLpNorm_diff2_le {p : ℝ≥0∞} (hp : 1 ≤ p) {g : ℝ → ℝ} (hg : Measurable g) {h : ℝ}
    (hpos : 0 < h) :
    eLpNorm ((Icc (0 : ℝ) (1 - 2 * h)).indicator (diff2 h g)) p volume ≤
      4 * eLpNorm g p vol01 := by
  have hGm := Gbound_measurable hg
  have hmono : eLpNorm ((Icc (0 : ℝ) (1 - 2 * h)).indicator (diff2 h g)) p volume ≤
      eLpNorm (fun x : ℝ => Gbound g (x + 2 * h) + 2 * Gbound g (x + h) + Gbound g x) p volume :=
    eLpNorm_mono_real (fun x => pt_bound hpos x)
  have h3 := eLpNorm_three_terms hp hGm h
  have hE : eLpNorm (Gbound g) p volume = eLpNorm g p vol01 := eLpNorm_indicator_norm p g
  rw [hE] at h3
  exact hmono.trans h3

/-- Cota `ω_p(g, t) ≤ 4‖g‖_{L^p([0,1])}` (axioma (b) do arcabouço). -/
theorem wtP_le_four {p : ℝ≥0∞} (hp : 1 ≤ p) (t : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    wtP p t g ≤ 4 * eLpNorm g p vol01 := by
  unfold wtP
  refine iSup₂_le fun h hh => ?_
  have hpos : 0 < h := hh.1
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_Icc (a := 0) (b := 1 - 2 * h))]
  exact eLpNorm_diff2_le hp hg hpos

/-- Desigualdade inversa em `L^p` (Proposição `lp:prop:inverse`):
`ω_p(f, 1/N) ≤ 4 R_N^G(f)_p`. -/
theorem wtP_le_four_realP {p : ℝ≥0∞} (hp : 1 ≤ p) (G : ℕ → Set (ℝ → ℝ)) (N : ℕ)
    {f : ℝ → ℝ} (hf : Measurable f) (hG : ∀ g ∈ G N, Measurable g) :
    wtP p (1 / (N : ℝ)) f ≤ 4 * realP p G N f := by
  have key : ∀ g ∈ G N, wtP p (1 / (N : ℝ)) f ≤
      4 * (distP p f g + wtP p (1 / (N : ℝ)) g) := by
    intro g hg
    have hfg : f = (f - g) + g := by funext x; simp
    have hgm := hG g hg
    have hfgm : Measurable (f - g) := hf.sub hgm
    have hsub : wtP p (1 / (N : ℝ)) f ≤
        wtP p (1 / (N : ℝ)) (f - g) + wtP p (1 / (N : ℝ)) g := by
      conv_lhs => rw [hfg]
      exact wtP_add_le hp _ hfgm hgm
    have hb : wtP p (1 / (N : ℝ)) (f - g) ≤ 4 * distP p f g :=
      wtP_le_four hp _ hfgm
    calc wtP p (1 / (N : ℝ)) f
        ≤ wtP p (1 / (N : ℝ)) (f - g) + wtP p (1 / (N : ℝ)) g := hsub
      _ ≤ 4 * distP p f g + wtP p (1 / (N : ℝ)) g := add_le_add hb le_rfl
      _ ≤ 4 * distP p f g + 4 * wtP p (1 / (N : ℝ)) g :=
          add_le_add le_rfl (le_mul_of_one_le_left (zero_le (wtP p (1 / (N : ℝ)) g))
            (by norm_num : (1 : ℝ≥0∞) ≤ 4))
      _ = 4 * (distP p f g + wtP p (1 / (N : ℝ)) g) := by rw [mul_add]
  unfold realP
  calc wtP p (1 / (N : ℝ)) f
      ≤ ⨅ g ∈ G N, 4 * (distP p f g + wtP p (1 / (N : ℝ)) g) :=
        le_iInf₂ fun g hg => key g hg
    _ = 4 * ⨅ g ∈ G N, (distP p f g + wtP p (1 / (N : ℝ)) g) := by
        have h4z : (4 : ℝ≥0∞) ≠ 0 := by norm_num
        have h4t : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
        simp only [ENNReal.mul_iInf_of_ne h4z h4t]

end FormalizacaoLp
