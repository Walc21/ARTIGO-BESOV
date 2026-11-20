import Formalizacao.UnifTheorem

/-!
# Piso aritmético em `L^p` (seção 6.2)

A integral do erro assinado em cada folha é o comprimento da folha vezes o erro no centro.
A desigualdade para o valor absoluto da integral dá o piso em `L^1`, e a monotonia do expoente
num espaço de probabilidade estende a cota a `L^p`.
-/

open scoped ENNReal
open MeasureTheory Set Artigo FormalizacaoLp FormalizacaoLow

namespace FormalizacaoFloor

/-- Constante que fica no meio da lacuna entre zero e o menor racional positivo admissível. -/
noncomputable def floorValue (H : ℕ) : ℝ := 1 / (2 * (H : ℝ))

private lemma floorValue_nonneg (H : ℕ) : 0 ≤ floorValue H := by
  unfold floorValue
  positivity

private lemma floorValue_le_abs_sub {H : ℕ} (hH : 1 ≤ H) {y : ℚ} (hy : ht y ≤ H) :
    floorValue H ≤ |floorValue H - y| := by
  have h₀ : (0 : ℝ) < H := by exact_mod_cast hH
  rcases le_or_gt y 0 with h | h
  · have hy₀ : (y : ℝ) ≤ 0 := by exact_mod_cast h
    exact (show floorValue H ≤ floorValue H - (y : ℝ) by linarith).trans (le_abs_self _)
  · have hy₁ := Pendencias.Agenda.inv_le_of_ht h hy
    have he : 2 * floorValue H = 1 / (H : ℝ) := by unfold floorValue; field_simp
    rw [abs_sub_comm]
    exact (show floorValue H ≤ (y : ℝ) - floorValue H by linarith).trans (le_abs_self _)

/-- Distância exata da constante de teste ao conjunto de racionais de altura limitada. -/
theorem rational_arithmetic_floor {H : ℕ} (hH : 1 ≤ H) :
    Metric.infDist (floorValue H) ((fun y : ℚ ↦ (y : ℝ)) '' Pendencias.Agenda.QH H) =
      floorValue H := by
  have hz : (0 : ℝ) ∈ (fun y : ℚ ↦ (y : ℝ)) '' Pendencias.Agenda.QH H :=
    ⟨0, by simpa [Pendencias.Agenda.QH, ht] using hH, by simp⟩
  apply le_antisymm
  · simpa [Real.dist_eq, abs_of_nonneg (floorValue_nonneg H)]
      using Metric.infDist_le_dist_of_mem (x := floorValue H) hz
  · rw [Metric.le_infDist ⟨0, hz⟩]
    rintro _ ⟨y, hy, rfl⟩
    rw [Real.dist_eq]
    exact floorValue_le_abs_sub hH hy

private lemma signed_leaf_integral (a : Atom) (v : ℝ) :
    (∫ x in cL a.k a.m..cR a.k a.m, (v - a.eval x)) =
      (cR a.k a.m - cL a.k a.m) * (v - a.y0) := by
  have hcent : (a.x0 : ℝ) = (cL a.k a.m + cR a.k a.m) / 2 := by
    simp only [Atom.x0, Rat.cast_div, Rat.cast_add, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_one, cL, cR]
    ring
  have he : (fun x : ℝ ↦ v - a.eval x) =
      fun x ↦ (v - (a.y0 : ℝ) + a.s * (a.x0 : ℝ)) - (a.s : ℝ) * x := by
    funext x
    simp only [Atom.eval]
    ring
  rw [he, intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((show Continuous (fun x : ℝ ↦ (a.s : ℝ) * x) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
    smul_eq_mul, hcent]
  ring

private lemma leaf_floor {H : ℕ} (hH : 1 ≤ H) (a : Atom) (ha : a.height ≤ H) :
    ENNReal.ofReal (floorValue H) * volume (Ioc (cL a.k a.m) (cR a.k a.m)) ≤
      ∫⁻ x in Ioc (cL a.k a.m) (cR a.k a.m), ‖floorValue H - a.eval x‖ₑ := by
  let v := floorValue H
  let l := cL a.k a.m
  let r := cR a.k a.m
  have hlr : l ≤ r := (cL_lt_cR _ _).le
  have hcont : Continuous (fun x : ℝ ↦ ‖v - a.eval x‖) := by unfold Atom.eval; fun_prop
  have hi : IntegrableOn (fun x ↦ ‖v - a.eval x‖) (Ioc l r) :=
    (hcont.intervalIntegrable l r).1
  have hj := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := fun x ↦ v - a.eval x) hlr
  rw [signed_leaf_integral, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlr),
    intervalIntegral.integral_of_le hlr] at hj
  have hp := mul_le_mul_of_nonneg_left
    (floorValue_le_abs_sub hH (a.ht_y0_le_height.trans ha)) (sub_nonneg.mpr hlr)
  have hk : (r - l) * v ≤ ∫ x in Ioc l r, ‖v - a.eval x‖ := hp.trans hj
  rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (floorValue_nonneg H), mul_comm]
  refine (ENNReal.ofReal_le_ofReal hk).trans_eq ?_
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)]
  exact lintegral_congr fun x ↦ ofReal_norm_eq_enorm (v - a.eval x)

private lemma tree_floor {H : ℕ} (hH : 1 ≤ H) (T : LTree) {k : ℕ} {m : ℤ}
    (hw : T.WF k m) (hh : T.maxHeight ≤ H) :
    ENNReal.ofReal (floorValue H) * volume (Ioc (cL k m) (cR k m)) ≤
      ∫⁻ x in Ioc (cL k m) (cR k m), ‖floorValue H - T.eval k m x‖ₑ := by
  induction T generalizing k m with
  | leaf a =>
    obtain ⟨rfl, rfl⟩ := hw
    exact leaf_floor hH a ((LTree.maxHeight_le_iff.mp hh) a (by simp [LTree.leaves]))
  | node l r ihl ihr =>
    let mid := cL (k + 1) (2 * m + 1)
    have hleft : cL k m ≤ mid := by
      dsimp only [mid]
      rw [← cR_child_left, ← cL_child_left]; exact (cL_lt_cR _ _).le
    have hright : mid ≤ cR k m := by rw [← cR_child_right]; exact (cL_lt_cR _ _).le
    have hl := ihl hw.1 (LTree.maxHeight_le_iff.mpr fun a ha ↦
      LTree.maxHeight_le_iff.mp hh a (List.mem_append_left _ ha))
    have hr := ihr hw.2.1 (LTree.maxHeight_le_iff.mpr fun a ha ↦
      LTree.maxHeight_le_iff.mp hh a (List.mem_append_right _ ha))
    rw [cL_child_left, cR_child_left] at hl
    rw [cR_child_right] at hr
    rw [← Ioc_union_Ioc_eq_Ioc hleft hright, measure_union
      (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc, mul_add,
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
    apply add_le_add
    · refine hl.trans_eq (lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).mpr ?_))
      filter_upwards [] with x hx
      change x ∈ Ioc (cL k m) mid at hx
      rcases hx.2.lt_or_eq with h | h
      · rw [LTree.eval, if_pos h]
      · rw [h, LTree.eval, if_neg (lt_irrefl _), LTree.eval_at_left hw.2.1]
        dsimp only [mid]
        rw [
          ← cR_child_left k m, LTree.eval_at_right hw.1, hw.2.2]
    · refine hr.trans_eq (lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).mpr ?_))
      filter_upwards [] with x hx
      change x ∈ Ioc mid (cR k m) at hx
      rw [LTree.eval, if_neg (not_lt.mpr hx.1.le)]

private lemma vol01_univ : vol01 univ = 1 := by simp [vol01, Real.volume_Icc]

/-- Proposição do piso aritmético para toda a biblioteca apontada, qualquer que seja `N`. -/
theorem arithmetic_floor_lp {p : ℝ≥0∞} (hp : 1 ≤ p) {N H : ℕ} (hH : 1 ≤ H)
    {g : ℝ → ℝ} (hg : g ∈ Pendencias.Agenda.Sigma (fun _ ↦ H) N) :
    ENNReal.ofReal (floorValue H) ≤ distP p (fun _ ↦ floorValue H) g := by
  letI : IsProbabilityMeasure vol01 := ⟨vol01_univ⟩
  have hmeas : Measurable ((fun _ : ℝ ↦ floorValue H) - g) :=
    measurable_const.sub (measurable_sigma hg)
  refine le_trans ?_ (eLpNorm_le_eLpNorm_of_exponent_le hp hmeas.aestronglyMeasurable)
  rw [eLpNorm_one_eq_lintegral_enorm]
  rcases hg with rfl | ⟨T, ⟨hw, _, hh⟩, rfl⟩
  · simp [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
      abs_of_nonneg (floorValue_nonneg H)]
  · have h := tree_floor hH T hw hh
    rwa [show cL 0 0 = 0 by norm_num [cL], show cR 0 0 = 1 by norm_num [cR],
      Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one, restrict_Ioc_eq_restrict_Icc] at h

/-- Melhor erro em `L^p` com a biblioteca apontada sob o orçamento `(N,H)`. -/
noncomputable def bestError (p : ℝ≥0∞) (N H : ℕ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ g ∈ Pendencias.Agenda.Sigma (fun _ ↦ H) N, distP p f g

theorem arithmetic_floor_bestError {p : ℝ≥0∞} (hp : 1 ≤ p) (N : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    ENNReal.ofReal (floorValue H) ≤ bestError p N H (fun _ ↦ floorValue H) :=
  le_iInf₂ fun _ hg ↦ arithmetic_floor_lp hp hH hg

private lemma besovNorm_const {p q : ℝ≥0∞} (hp : p ≠ 0) (hq : 0 < q) (s a : ℝ) :
    besovNorm p s q (fun _ ↦ a) = ENNReal.ofReal |a| := by
  have hz (t : ℝ) : wtP p t (fun _ ↦ a) = 0 := by
    have hh (h : ℝ) : diff2 h (fun _ ↦ a) = 0 := by funext x; simp [diff2]; ring
    simp [wtP, hh]
  have hs : FormalizacaoRed.besovSeq p s (fun _ ↦ a) = 0 := by
    funext k; simp [FormalizacaoRed.besovSeq, hz]
  have hzq : lqNorm q (0 : ℕ → ℝ≥0∞) = 0 := FormalizacaoLq.lqNorm_zero hq
  have hμ : vol01 ≠ 0 := by
    intro h
    have he := vol01_univ
    simp [h] at he
  rw [besovNorm, hs, hzq, add_zero, eLpNorm_const a hp hμ]
  simp [← ofReal_norm_eq_enorm, Real.norm_eq_abs]

/-- Necessidade de `H(N) ≥ N^s/(2C)` sob uma taxa uniforme na bola unitária. -/
theorem arithmetic_height_necessary {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 0 < q) {s C : ℝ}
    (hC : 0 < C) (H : ℕ → ℕ) {N : ℕ} (hN : 1 ≤ N) (hH : 2 ≤ H N)
    (hrate : ∀ f : ℝ → ℝ, Measurable f → besovNorm p s q f ≤ 1 →
      realP p (Pendencias.Agenda.Sigma H) N f ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-s))) :
    (N : ℝ) ^ s / (2 * C) ≤ H N := by
  have hHr : (1 : ℝ) ≤ H N := by exact_mod_cast (show 1 ≤ H N by omega)
  have ha : floorValue (H N) ≤ 1 := by
    unfold floorValue
    rw [div_le_one (by positivity)]
    linarith
  have hb : besovNorm p s q (fun _ ↦ floorValue (H N)) ≤ 1 := by
    rw [besovNorm_const (ne_of_gt (zero_lt_one.trans_le hp)) hq,
      abs_of_nonneg (floorValue_nonneg _), ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ha
  have hl : ENNReal.ofReal (floorValue (H N)) ≤
      realP p (Pendencias.Agenda.Sigma H) N (fun _ ↦ floorValue (H N)) :=
    le_iInf₂ fun g hg ↦ (arithmetic_floor_lp hp (by omega) hg).trans le_self_add
  have hh := hl.trans (hrate _ measurable_const hb)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ C * (N : ℝ) ^ (-s)),
    floorValue, Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    div_le_div_iff₀ (by positivity) (by positivity)] at hh
  rw [div_le_iff₀ (by positivity)]
  linarith

end FormalizacaoFloor
