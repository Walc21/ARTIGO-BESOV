import Formalizacao.MinimaxDefs
import Formalizacao.AlturaCritical3
import Formalizacao.L1LinearHeight

/-!
# Cota superior minimax em folhas e altura

A construção diádica usa constantes independentes do alvo e da escala.
O arredondamento da escala permite impor os dois orçamentos inteiros em separado.
-/

open scoped ENNReal
open MeasureTheory Set
open FormalizacaoLp FormalizacaoLow FormalizacaoFloor FormalizacaoRed

namespace FormalizacaoMinimax

/-- Aumentar qualquer um dos orçamentos preserva a admissibilidade da mesma árvore. -/
theorem classNH_mono {n N h H : ℕ} (hn : n ≤ N) (hh : h ≤ H) :
    classNH n h ⊆ classNH N H := by
  rintro g ⟨T, ⟨hwf, hleaves, hheight⟩, rfl⟩
  exact ⟨T, ⟨hwf, hleaves.trans hn, hheight.trans hh⟩, rfl⟩

/-- A classe usada em `bestError` também é crescente nos dois orçamentos. -/
theorem sigma_const_mono {n N h H : ℕ} (hn : n ≤ N) (hh : h ≤ H) :
    Pendencias.Agenda.Sigma (fun _ ↦ h) n ⊆ Pendencias.Agenda.Sigma (fun _ ↦ H) N := by
  intro g hg
  rcases hg with hg | hg
  · exact Or.inl hg
  · exact Or.inr (classNH_mono hn hh (show g ∈ classNH n h from hg))

private lemma bestError_le_dist {p : ℝ≥0∞} {N H : ℕ} {f g : ℝ → ℝ}
    (hg : g ∈ Pendencias.Agenda.Sigma (fun _ ↦ H) N) :
    bestError p N H f ≤ distP p f g :=
  iInf₂_le g hg

private lemma modulus_unit_ball {p : ℝ≥0∞} {s : ℝ} {q : ℝ≥0∞} (hq : 0 < q)
    {f : ℝ → ℝ} (hb : besovNorm p s q f ≤ 1) (r : ℕ) :
    wtP p (1 / (2 : ℝ) ^ r) f ≤ ENNReal.ofReal (((2 : ℝ) ^ r) ^ (-s)) := by
  let x : ℝ := (2 : ℝ) ^ ((r : ℝ) * s)
  have hx : 0 < x := by dsimp [x]; positivity
  have ht : ENNReal.ofReal x * wtP p (1 / (2 : ℝ) ^ r) f ≤ 1 :=
    (FormalizacaoCrit2.term_le_lqNorm hq (besovSeq p s f) r).trans
      ((lqNorm_le_besovNorm p s q f).trans hb)
  have hinv : x⁻¹ = ((2 : ℝ) ^ r) ^ (-s) := by
    rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast (2 : ℝ) r,
      ← Real.rpow_mul (by norm_num)]
  rw [← hinv, ← one_div, ENNReal.ofReal_div_of_pos hx, ENNReal.ofReal_one]
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl (by simpa using hx)) (Or.inl ENNReal.ofReal_ne_top)).2 (by simpa [mul_comm] using ht)

private lemma add_modulus_bound {p : ℝ≥0∞} {s CW K : ℝ} {q : ℝ≥0∞} (hq : 0 < q)
    {f : ℝ → ℝ} (hb : besovNorm p s q f ≤ 1) (hCW : 0 ≤ CW) (hK : 0 ≤ K) (r : ℕ) :
    9 * ENNReal.ofReal CW * wtP p (1 / (2 : ℝ) ^ r) f +
      ENNReal.ofReal (K * ((2 : ℝ) ^ r) ^ (-s)) ≤
        ENNReal.ofReal ((9 * CW + K) * ((2 : ℝ) ^ r) ^ (-s)) := by
  refine add_le_add (mul_le_mul_right (modulus_unit_ball hq hb r) _) le_rfl |>.trans ?_
  rw [add_mul, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 9 * CW),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9), ENNReal.ofReal_ofNat]

open FormalizacaoCrit2 FormalizacaoCrit3 FormalizacaoLqAux in
/-- No ponto crítico com `p > 1`, a altura é linear para todo `q > 0`, inclusive `q = ∞`. -/
theorem critical_upper_dyadic {p : ℝ} (hp : 1 < p) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧ ∀ (f : ℝ → ℝ), Measurable f →
      besovNorm (ENNReal.ofReal p) (1 / p) q f ≤ 1 →
      ∀ r : ℕ, 1 ≤ r → ∀ H : ℕ, A * (2 : ℝ) ^ r ≤ H →
        ∃ g ∈ classNH (2 ^ r) H,
          distP (ENNReal.ofReal p) f g ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ r) ^ (-(1 / p))) := by
  obtain ⟨CW, hCW, hW⟩ := FormalizacaoW.whitney_lp hp.le
  let A := Avc p CW
  have hA : 0 < A := Avc_pos hp hCW
  have hCM : 0 ≤ CMc p CW := CM_nonneg hp hCW
  let ρ := (2 : ℝ) ^ (1 / p - 1)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hs : 1 / p < 1 := (div_lt_one (by linarith : 0 < p)).2 hp
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨K, hK, hgeom⟩ := poly_geom_majorant hρ hρ1
  let D : ℝ := 8 * CMc p CW * ρ / A * K + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨max 1 (3 * A), 9 * CW + D, le_max_left .., by positivity, ?_⟩
  intro f hf hb r hr H hH
  have hb' : besovNorm (ENNReal.ofReal p) (1 / p) q f ≤ ENNReal.ofReal 1 := by simpa using hb
  obtain ⟨hNp, _, _, hfin, _, _⟩ := ball_bounds hp.le hq zero_le_one hf hb'
  have hmem : MemLp f (ENNReal.ofReal p) vol01 := ⟨hf.aestronglyMeasurable, hfin⟩
  have hfi : IntegrableOn f (Icc 0 1) := hmem.integrable (ENNReal.one_le_ofReal.2 hp.le)
  have hW2 : (wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal ≤ 1 := by
    have hw := ENNReal.toReal_mono ENNReal.ofReal_ne_top (modulus_unit_ball hq hb 1)
    rw [pow_one, ENNReal.toReal_ofReal (by positivity)] at hw
    exact hw.trans (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
      have : 0 < 1 / p := by positivity
      linarith))
  have hB0 : B0 p CW f ≤ C0c p CW * 1 := B0_le hp.le hCW hf hfin zero_le_one hNp hW2
  have hH' : A * (1 + 1) * (((2 ^ r : ℕ) : ℝ) + 1) ≤ H := by
    have hn : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
      exact_mod_cast (show 2 ≤ 2 ^ r from
        (show 2 = 2 ^ (1 : ℕ) by norm_num).le.trans (Nat.pow_le_pow_right (by decide) hr))
    push_cast
    rw [mul_assoc, one_add_one_eq_two]
    refine (mul_le_mul_of_nonneg_left (show 2 * ((2 : ℝ) ^ r + 1) ≤ 3 * 2 ^ r by linarith)
      hA.le).trans ?_
    calc A * (3 * (2 : ℝ) ^ r) = (3 * A) * (2 : ℝ) ^ r := by ring
      _ ≤ max 1 (3 * A) * (2 : ℝ) ^ r := by gcongr; exact le_max_right ..
      _ ≤ H := hH
  have hceil : (criticalAgenda p CW 1 (2 ^ r) : ℝ) ≤ H := by
    exact Nat.cast_le.2 (Nat.ceil_le.2 hH' : criticalAgenda p CW 1 (2 ^ r) ≤ H)
  obtain ⟨hH1, hH2, hH3⟩ := level_conditions hp hCW zero_le_one hr hB0
  obtain ⟨T, hT, hd⟩ := critical_dist hp hW hCW hf hfi hfin zero_le_one
    (wr_le_of_besov hq hp.le hf zero_le_one hb' hfin) hr
    (hH1.trans hceil) (hH2.trans hceil) (hH3.trans hceil)
  let E : ℝ := 8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * 1 * r + 1) / H
  have hE : E ≤ D * ((2 : ℝ) ^ r) ^ (-(1 / p)) := by
    obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by omega⟩
    have hmaj := E_majorant hp hCW zero_le_one l hB0 hH'
    have hbound : (2 : ℝ) ^ (((l + 1 : ℕ) : ℝ) * (1 / p)) * E ≤ D := by
      refine hmaj.trans ?_
      have hgeo : ((l : ℝ) + 2) * ρ ^ l ≤ K := by simpa using hgeom l
      exact (mul_le_mul_of_nonneg_left hgeo (by positivity)).trans (by dsimp [D]; linarith)
    have hpow : ((2 : ℝ) ^ (l + 1 : ℕ)) ^ (-(1 / p)) =
        ((2 : ℝ) ^ (((l + 1 : ℕ) : ℝ) * (1 / p)))⁻¹ := by
      rw [← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_neg (by norm_num)]
      congr 1
      ring
    rw [hpow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    simpa only [mul_comm] using hbound
  refine ⟨T.eval 0 0, ⟨T, hT, rfl⟩, hd.trans ?_⟩
  rw [Nat.cast_pow, Nat.cast_ofNat]
  exact (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hE)).trans
    (add_modulus_bound hq hb hCW hD.le r)

private lemma upper_dyadic_off_critical {p s : ℝ} (hp : 1 ≤ p) (hs2 : s < 2)
    {q : ℝ≥0∞} (hq : 0 < q) (hne : s ≠ 1 / p) :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧ ∀ (f : ℝ → ℝ), Measurable f →
      besovNorm (ENNReal.ofReal p) s q f ≤ 1 →
      ∀ r : ℕ, 1 ≤ r → ∀ H : ℕ, A * ((2 : ℝ) ^ r) ^ aPS p s ≤ H →
        ∃ g ∈ classNH (2 ^ r) H,
          distP (ENNReal.ofReal p) f g ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ r) ^ (-s)) := by
  obtain ⟨CW, Cs, hCW, hCs, hu⟩ := uniform_besov_ball hp hq hs2
  let a := aPS p s
  have ha : 0 ≤ a := by rw [show a = nuHat p s from aPS_eq_nuHat hp]; exact nuHat_nonneg p s hp
  have hk : kapHat p s q 0 = 0 := by
    rcases lt_or_gt_of_ne hne with hl | hg
    · rw [kapHat, if_neg (not_lt.2 hl.le), if_pos hl]
    · rw [kapHat, if_pos hg]
  let A := 32 * (Cs + 1) * 2 * (2 : ℝ) ^ a
  refine ⟨max 1 A, 9 * CW + 1, le_max_left .., by positivity, ?_⟩
  intro f hf hb r hr H hH
  obtain ⟨g, hg, hd, he, _⟩ := (hu 0 le_rfl).1 1 le_rfl f hf (by simpa using hb) r hr
  have hbudget : Hunif (32 * (Cs + 1)) 1 (nuHat p s) (kapHat p s q 0) (2 ^ r) ≤ H := by
    unfold Hunif
    rw [← aPS_eq_nuHat hp, hk, Real.rpow_zero, mul_one, Nat.ceil_le]
    push_cast
    have hn : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    have hpow : ((2 : ℝ) ^ r + 1) ^ a ≤ (2 * (2 : ℝ) ^ r) ^ a :=
      Real.rpow_le_rpow (by positivity) (by linarith) ha
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hpow
    calc _ ≤ 32 * (Cs + 1) * (1 + 1) * ((2 : ℝ) ^ a * ((2 : ℝ) ^ r) ^ a) := by
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = A * ((2 : ℝ) ^ r) ^ a := by dsimp [A]; ring
      _ ≤ max 1 A * ((2 : ℝ) ^ r) ^ a := by gcongr; exact le_max_right ..
      _ ≤ H := hH
  exact ⟨g, classNH_mono le_rfl hbudget hg, hd.trans (by simpa using he)⟩

/-- Cota por escala diádica, uniforme na bola unitária e nos orçamentos admissíveis. -/
theorem upper_bound_dyadic {p s : ℝ} (hp : 1 ≤ p) (hs2 : s < 2) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧ ∀ (f : ℝ → ℝ), Measurable f →
      besovNorm (ENNReal.ofReal p) s q f ≤ 1 →
      ∀ r : ℕ, 1 ≤ r → ∀ H : ℕ, A * ((2 : ℝ) ^ r) ^ aPS p s ≤ H →
        ∃ g ∈ classNH (2 ^ r) H,
          distP (ENNReal.ofReal p) f g ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ r) ^ (-s)) := by
  by_cases hs : s = 1 / p
  · subst s
    have hmid : 1 / p ≤ 1 := (div_le_one (by linarith : 0 < p)).2 hp
    rw [aPS_of_mid le_rfl hmid]
    simp only [Real.rpow_one]
    rcases eq_or_lt_of_le hp with rfl | hp'
    · norm_num only [div_one, ENNReal.ofReal_one] at *
      obtain ⟨CW, CE, hCW, hCE, hl1⟩ := FormalizacaoAltura.l1_linear_height
      refine ⟨2 * CE, 9 * CW + 1, by linarith, by positivity, ?_⟩
      intro f hf hb r hr H hH
      obtain ⟨g, hg, hd⟩ := hl1 q hq 1 le_rfl f hf (by simpa using hb) r hr H (by
        simpa [show CE * (1 + 1) = 2 * CE by ring] using hH)
      have hHpos : 0 < (H : ℝ) := lt_of_lt_of_le (by positivity) hH
      have hE : CE * (1 + 1) / H ≤ 1 * ((2 : ℝ) ^ r) ^ (-(1 : ℝ)) := by
        rw [one_mul, Real.rpow_neg_one, div_le_iff₀ hHpos, mul_comm _ (H : ℝ),
          ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        simpa only [one_add_one_eq_two, mul_comm CE 2] using hH
      exact ⟨g, hg, hd.trans ((add_le_add le_rfl (ENNReal.ofReal_le_ofReal hE)).trans
        (add_modulus_bound hq hb hCW zero_le_one r))⟩
    · exact critical_upper_dyadic hp' hq
  · exact upper_dyadic_off_critical hp hs2 hq hs

/-- A maior potência de dois sob `X` está em `(X/2,X]` quando `X ≥ 2`. -/
theorem exists_dyadic_scale {X : ℝ} (hX : 2 ≤ X) :
    ∃ r : ℕ, 1 ≤ r ∧ X / 2 < (2 : ℝ) ^ r ∧ (2 : ℝ) ^ r ≤ X := by
  have hX0 : 0 < X := by linarith
  let r := ⌊Real.logb 2 X⌋₊
  have hlog : 1 ≤ Real.logb 2 X :=
    (Real.le_logb_iff_rpow_le (by norm_num) hX0).2 (by simpa using hX)
  have hr : 1 ≤ r := by
    apply (Nat.le_floor_iff (by linarith : 0 ≤ Real.logb 2 X)).2
    exact_mod_cast hlog
  have hleft : X < (2 : ℝ) ^ ((r : ℝ) + 1) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) hX0).1 (Nat.lt_floor_add_one _)
  rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one] at hleft
  have hright : (2 : ℝ) ^ (r : ℝ) ≤ X :=
    (Real.le_logb_iff_rpow_le (by norm_num) hX0).1 (Nat.floor_le (by linarith))
  exact ⟨r, hr, by linarith, by simpa only [Real.rpow_natCast] using hright⟩

/-- Cota superior do Teorema 5.2 para os dois orçamentos inteiros independentes. -/
theorem upper_bound_NH (p s : ℝ) (q : ℝ≥0∞) (hp : 1 ≤ p) (hs0 : 0 < s) (hs2 : s < 2)
    (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ N H : ℕ, 2 ≤ N → 2 ≤ H →
      Dfun p s q N H ≤ ENNReal.ofReal
        (C * ((N : ℝ) ^ (-s) + (H : ℝ) ^ (-s / aPS p s))) := by
  obtain ⟨A, D, hA, hD, hd⟩ := upper_bound_dyadic hp hs2 hq
  let a := aPS p s
  have ha : 0 < a := aPS_pos hp hs0
  have hA0 : 0 < A := by linarith
  let K := A ^ (s / a)
  have hK : 1 ≤ K := Real.one_le_rpow hA (by positivity)
  have hD1 : 1 ≤ D + 1 := by linarith
  let C : ℝ := (2 : ℝ) ^ s * (D + 1) * K
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun N H hN hH ↦ ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < (N : ℝ) := by linarith
  have hH0 : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  let Y := ((H : ℝ) / A) ^ a⁻¹
  have hY : 0 < Y := by dsimp [Y]; positivity
  let X := min (N : ℝ) Y
  have hYpow : Y ^ a = (H : ℝ) / A := Real.rpow_inv_rpow (by positivity) ha.ne'
  have hYneg : Y ^ (-s) = K * (H : ℝ) ^ (-s / a) := by
    dsimp [Y, K]
    rw [← Real.rpow_mul (by positivity), show a⁻¹ * -s = -s / a by ring,
      Real.div_rpow hH0.le hA0.le, neg_div, Real.rpow_neg hA0.le, div_inv_eq_mul, mul_comm]
  unfold Dfun
  refine iSup_le fun f ↦ iSup_le fun hf ↦ iSup_le fun hb ↦ ?_
  by_cases hX : 2 ≤ X
  · obtain ⟨r, hr, hhalf, hnX⟩ := exists_dyadic_scale hX
    have hnN : 2 ^ r ≤ N := by
      exact_mod_cast hnX.trans (min_le_left (N : ℝ) Y)
    have hnH : A * ((2 : ℝ) ^ r) ^ a ≤ H := by
      have h := Real.rpow_le_rpow (by positivity) (hnX.trans (min_le_right (N : ℝ) Y)) ha.le
      rw [hYpow] at h
      calc _ ≤ A * ((H : ℝ) / A) := mul_le_mul_of_nonneg_left h hA0.le
        _ = H := by field_simp
    obtain ⟨g, hg, hdist⟩ := hd f hf hb r hr H hnH
    refine (bestError_le_dist (sigma_const_mono hnN le_rfl (Or.inr hg))).trans (hdist.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have hscale : ((2 : ℝ) ^ r) ^ (-s) ≤ (2 : ℝ) ^ s * X ^ (-s) := by
      calc _ ≤ (X / 2) ^ (-s) := Real.rpow_le_rpow_of_nonpos (by linarith) hhalf.le (by linarith)
        _ = _ := by
          rw [Real.div_rpow (by linarith) (by norm_num),
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
    have hsum : X ^ (-s) ≤ (N : ℝ) ^ (-s) + Y ^ (-s) := by
      rcases le_total (N : ℝ) Y with h | h
      · dsimp [X]; rw [min_eq_left h]; exact le_add_of_nonneg_right (by positivity)
      · dsimp [X]; rw [min_eq_right h]; exact le_add_of_nonneg_left (by positivity)
    calc _ ≤ D * ((2 : ℝ) ^ s * X ^ (-s)) := mul_le_mul_of_nonneg_left hscale hD.le
      _ ≤ D * ((2 : ℝ) ^ s * ((N : ℝ) ^ (-s) + Y ^ (-s))) := by gcongr
      _ ≤ C * ((N : ℝ) ^ (-s) + (H : ℝ) ^ (-s / a)) := by
        rw [hYneg]
        dsimp [C]
        calc _ = (2 : ℝ) ^ s * (D * ((N : ℝ) ^ (-s) + K * (H : ℝ) ^ (-s / a))) := by ring
          _ ≤ (2 : ℝ) ^ s * ((D + 1) * (K * ((N : ℝ) ^ (-s) + (H : ℝ) ^ (-s / a)))) := by
            have hweighted : (N : ℝ) ^ (-s) + K * (H : ℝ) ^ (-s / a) ≤
                K * ((N : ℝ) ^ (-s) + (H : ℝ) ^ (-s / a)) := by
              rw [mul_add]
              exact add_le_add (le_mul_of_one_le_left (by positivity) hK) le_rfl
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul (by linarith) hweighted (by positivity) (by positivity))
              (by positivity)
          _ = _ := by ring
  · have hY2 : Y < 2 := by
      by_contra! hY2
      exact hX (le_min hN2 hY2)
    have hsmall : 1 ≤ (2 : ℝ) ^ s * Y ^ (-s) := by
      calc 1 = (2 : ℝ) ^ s * (2 : ℝ) ^ (-s) := by
            rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hY hY2.le (by linarith)) (by positivity)
    have hzero : (0 : ℝ → ℝ) ∈ Pendencias.Agenda.Sigma (fun _ ↦ H) N := Or.inl rfl
    refine (bestError_le_dist hzero).trans ?_
    rw [distP, sub_zero]
    refine ((eLpNorm_le_besovNorm _ s q f).trans hb).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [hYneg] at hsmall
    refine hsmall.trans ?_
    dsimp [C]
    calc _ ≤ (2 : ℝ) ^ s * ((D + 1) * (K * (H : ℝ) ^ (-s / a))) := by
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hD1)
            (by positivity)
      _ = (2 : ℝ) ^ s * (D + 1) * K * (H : ℝ) ^ (-s / a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity))
        (by positivity)

end FormalizacaoMinimax
