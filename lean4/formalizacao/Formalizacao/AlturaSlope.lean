import Formalizacao.AlturaFloor

/-!
# Piso de inclinação (auditoria, Parte II, Teorema 2.3 do relatório)

Para `s ≤ 1/p`, a função `f_t(x) = a φB((x - 1/4)/t)` tem, em dois intervalos disjuntos
`I = [1/4 + t/4, 1/4 + t/2]` e `I + t`, valores `a` e `0`. Uma função `H`-Lipschitz `g` com
`H t ≤ a/2` satisfaz `|f - g|(x) + |f - g|(x+t) ≥ a/2` em `I`. Integrando, obtém-se
`‖f - g‖_{L^p} ≥ c_p a t^{1/p}`, e a escolha `a = c t^{-δ}` (`δ = 1/p - s`) dá o piso
`c_L H^{-β}` com `β = s/(1+δ)`.
-/

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace FormalizacaoAltura

open Artigo FormalizacaoLp FormalizacaoLow

/-! ## Pontual: dois intervalos -/

/-- Em `I`, a função-teste vale `a` e em `x+t` vale `0`; então `|f-g|(x) + |f-g|(x+t) ≥ a/2`. -/
lemma two_interval_pointwise {a t H : ℝ} (ht : 0 < t) (ht4 : t ≤ 1 / 4) (hHt : H * t ≤ a / 2)
    {g : ℝ → ℝ} (hg : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |g x - g y| ≤ H * |x - y|)
    {x : ℝ} (hx : x ∈ Icc (1 / 4 + t / 4) (1 / 4 + t / 2)) :
    a / 2 ≤ |bumpS φB a (1 / 4) t x - g x| + |bumpS φB a (1 / 4) t (x + t) - g (x + t)| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hf1 : bumpS φB a (1 / 4) t x = a := by
    unfold bumpS
    have hmem : (x - 1 / 4) / t ∈ Icc (1 / 4 : ℝ) (1 / 2) := by
      constructor
      · rw [le_div_iff₀ ht]; linarith
      · rw [div_le_iff₀ ht]; linarith
    rw [φB_one_of_mem hmem, mul_one]
  have hf2 : bumpS φB a (1 / 4) t (x + t) = 0 := by
    unfold bumpS
    apply mul_eq_zero_of_right
    apply φB_eq_zero_of_not_mem
    intro h
    have : (x + t - 1 / 4) / t ≥ 5 / 4 := by
      rw [ge_iff_le, le_div_iff₀ ht]; linarith
    have hlt : (x + t - 1 / 4) / t < 5 / 8 := by
      have := h.2
      have e : (x + t - 1 / 4) / t = (x + t - 1 / 4) / t := rfl
      linarith [h.2]
    linarith
  have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hxt01 : x + t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hlip := hg x hx01 (x + t) hxt01
  have hdiff : |x - (x + t)| = t := by rw [show x - (x + t) = -t by ring, abs_neg, abs_of_pos ht]
  rw [hdiff] at hlip
  -- `a = (f x - g x) - (f(x+t) - g(x+t)) + (g x - g(x+t))`
  have hid : a = (bumpS φB a (1 / 4) t x - g x) - (bumpS φB a (1 / 4) t (x + t) - g (x + t)) +
      (g x - g (x + t)) := by
    rw [hf1, hf2]; ring
  have htri : a ≤ |bumpS φB a (1 / 4) t x - g x| + |bumpS φB a (1 / 4) t (x + t) - g (x + t)| +
      |g x - g (x + t)| := by
    have h1 := le_abs_self (bumpS φB a (1 / 4) t x - g x)
    have h2 := neg_le_abs (bumpS φB a (1 / 4) t (x + t) - g (x + t))
    have h3 := le_abs_self (g x - g (x + t))
    linarith
  have hHt' : H * t ≤ a / 2 := hHt
  have hlip' : |g x - g (x + t)| ≤ a / 2 := hlip.trans hHt'
  linarith

/-! ## Passagem à norma `L^p` -/

/-- Convexidade de `ℓ^Q`: `(z₁+z₂)^Q ≤ 2^{Q-1}(z₁^Q + z₂^Q)`. -/
lemma enn_pair_le {Q : ℝ} (hQ : 1 ≤ Q) (u v c : ℝ≥0∞) (h : c ≤ u + v) :
    c ^ Q ≤ 2 ^ (Q - 1) * (u ^ Q + v ^ Q) :=
  (ENNReal.rpow_le_rpow h (by linarith)).trans (ENNReal.rpow_add_le_mul_rpow_add_rpow u v hQ)

/-- Integral de `G = ‖u‖ₑ^Q` sobre `I` e `I+t`: piso `ofReal(κ₀ t/4) ≤ 2^{Q-1} ∫_{[0,1]} G`. -/
lemma lintegral_pair_lower {Q : ℝ} (hQ : 1 ≤ Q) {u : ℝ → ℝ} (hu : Measurable u) {t : ℝ}
    (ht : 0 < t) (ht4 : t ≤ 1 / 4) {κ0 : ℝ} (hκ : 0 ≤ κ0)
    (hpt : ∀ x ∈ Icc (1 / 4 + t / 4) (1 / 4 + t / 2),
      ENNReal.ofReal κ0 ≤ 2 ^ (Q - 1) * (‖u x‖ₑ ^ Q + ‖u (x + t)‖ₑ ^ Q)) :
    ENNReal.ofReal (κ0 * (t / 4)) ≤ 2 ^ (Q - 1) * ∫⁻ y in Icc (0 : ℝ) 1, ‖u y‖ₑ ^ Q := by
  set I : Set ℝ := Icc (1 / 4 + t / 4) (1 / 4 + t / 2) with hI
  set K : Set ℝ := Icc (1 / 4 + t / 4 + t) (1 / 4 + t / 2 + t) with hK
  set G : ℝ → ℝ≥0∞ := fun y => ‖u y‖ₑ ^ Q with hG
  have hGm : Measurable G := by
    rw [hG]; exact (hu.enorm).pow_const Q
  have hIm : MeasurableSet I := measurableSet_Icc
  have hKm : MeasurableSet K := measurableSet_Icc
  -- translação: `∫_I G(x+t) = ∫_K G`
  have hshift : ∫⁻ x in I, G (x + t) = ∫⁻ y in K, G y := by
    rw [← lintegral_indicator hIm, ← lintegral_indicator hKm]
    have hpt' : ∀ x, I.indicator (fun x => G (x + t)) x = K.indicator G (x + t) := by
      intro x
      by_cases hx : x ∈ I
      · have hxK : x + t ∈ K := by
          obtain ⟨h1, h2⟩ := hx
          exact ⟨by linarith [h1, h2], by linarith [h1, h2]⟩
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxK]
      · have hxK : x + t ∉ K := by
          intro hK'
          apply hx
          obtain ⟨h1, h2⟩ := hK'
          exact ⟨by linarith, by linarith⟩
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxK]
    simp_rw [hpt']
    exact lintegral_add_right_eq_self (K.indicator G) t
  -- união disjunta
  have hdisj : Disjoint I K := by
    rw [Set.disjoint_left]
    intro x hxI hxK
    obtain ⟨_, h2⟩ := hxI
    obtain ⟨h3, _⟩ := hxK
    linarith
  have hsub : I ∪ K ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hunion : ∫⁻ y in I ∪ K, G y = (∫⁻ y in I, G y) + ∫⁻ y in K, G y := by
    rw [Measure.restrict_union hdisj hKm, lintegral_add_measure]
  have hle_union : ∫⁻ y in I ∪ K, G y ≤ ∫⁻ y in Icc (0 : ℝ) 1, G y := lintegral_mono_set hsub
  -- minoração pontual integrada em `I`
  have hlow : ∫⁻ x in I, ENNReal.ofReal κ0 ≤ ∫⁻ x in I, 2 ^ (Q - 1) * (G x + G (x + t)) := by
    apply setLIntegral_mono
    · exact measurable_const.mul (hGm.add (hGm.comp (measurable_id.add_const t)))
    · intro x hx
      have := hpt x hx
      simpa [hG] using this
  have hconst : ∫⁻ x in I, ENNReal.ofReal κ0 = ENNReal.ofReal (κ0 * (t / 4)) := by
    rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hκ]
    congr 2; ring
  have hfin : (2 : ℝ≥0∞) ^ (Q - 1) ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  have e1 : ∫⁻ x in I, (G x + G (x + t)) = (∫⁻ x in I, G x) + ∫⁻ x in I, G (x + t) :=
    lintegral_add_left (μ := volume.restrict I) hGm (fun x => G (x + t))
  have hsplit : ∫⁻ x in I, 2 ^ (Q - 1) * (G x + G (x + t)) =
      2 ^ (Q - 1) * ((∫⁻ y in I, G y) + ∫⁻ y in K, G y) := by
    rw [lintegral_const_mul' _ _ hfin, e1, hshift]
  calc ENNReal.ofReal (κ0 * (t / 4)) = ∫⁻ x in I, ENNReal.ofReal κ0 := hconst.symm
    _ ≤ ∫⁻ x in I, 2 ^ (Q - 1) * (G x + G (x + t)) := hlow
    _ = 2 ^ (Q - 1) * ((∫⁻ y in I, G y) + ∫⁻ y in K, G y) := hsplit
    _ = 2 ^ (Q - 1) * ∫⁻ y in I ∪ K, G y := by rw [hunion]
    _ ≤ 2 ^ (Q - 1) * ∫⁻ y in Icc (0 : ℝ) 1, G y := by gcongr
    _ = 2 ^ (Q - 1) * ∫⁻ y in Icc (0 : ℝ) 1, ‖u y‖ₑ ^ Q := rfl

/-! ## Cotas finais -/

/-- Constante `c_p = (1/2)(1/(4·2^{Q-1}))^{1/Q}` do piso de inclinação. -/
noncomputable def cpConst (Q : ℝ) : ℝ := (1 / 2) * (1 / (4 * 2 ^ (Q - 1))) ^ Q⁻¹

/-- Cota de `L^p` a partir da integral: `K^{1/Q} ≤ ‖u‖_{L^p([0,1])}` quando `K ≤ ∫⁻_{[0,1]} |u|^Q`. -/
lemma eLpNorm_ge_of_lintegral {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {u : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (h : ENNReal.ofReal K ≤ ∫⁻ y in Icc (0 : ℝ) 1, ‖u y‖ₑ ^ p.toReal) :
    ENNReal.ofReal (K ^ p.toReal⁻¹) ≤ eLpNorm u p (volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, one_div,
    ← ENNReal.ofReal_rpow_of_nonneg hK (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  exact ENNReal.rpow_le_rpow h (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- **Piso de inclinação (uma distância).** Para `g` `H`-Lipschitz em `[0,1]` com `H t ≤ a/2`:
`dist_{L^p}(a φB((· - 1/4)/t), g) ≥ c_p a t^{1/p}`. -/
lemma slope_dist_lower {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) {H : ℝ} {g : ℝ → ℝ}
    (hgm : Measurable g)
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |g x - g y| ≤ H * |x - y|)
    {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) (ht4 : t ≤ 1 / 4) (hHt : H * t ≤ a / 2) :
    ENNReal.ofReal (a * t ^ p.toReal⁻¹ * cpConst p.toReal) ≤
      distP p (bumpS φB a (1 / 4) t) g := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  set Q := p.toReal with hQdef
  have hQ : 1 ≤ Q := by
    have := ENNReal.toReal_mono hpt hp1; simpa using this
  have hQ0 : Q ≠ 0 := by linarith
  have hfm : Measurable (bumpS φB a (1 / 4) t) := by
    have hc : Continuous (bumpS φB a (1 / 4) t) := by
      unfold bumpS
      exact continuous_const.mul (φB_smooth.continuous.comp
        ((continuous_id.sub continuous_const).div_const t))
    exact hc.measurable
  have hum : Measurable (fun x => bumpS φB a (1 / 4) t x - g x) := hfm.sub hgm
  have ha2 : 0 ≤ a / 2 := by linarith
  have hκ0nn : 0 ≤ (a / 2) ^ Q := Real.rpow_nonneg ha2 _
  have hpt' : ∀ x ∈ Icc (1 / 4 + t / 4) (1 / 4 + t / 2),
      ENNReal.ofReal ((a / 2) ^ Q) ≤
        2 ^ (Q - 1) * (‖bumpS φB a (1 / 4) t x - g x‖ₑ ^ Q +
          ‖bumpS φB a (1 / 4) t (x + t) - g (x + t)‖ₑ ^ Q) := by
    intro x hx
    have hpair := two_interval_pointwise ht ht4 hHt hg hx
    have hsum : ENNReal.ofReal (a / 2) ≤
        ‖bumpS φB a (1 / 4) t x - g x‖ₑ + ‖bumpS φB a (1 / 4) t (x + t) - g (x + t)‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (abs_nonneg _)
        (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hpair
    have hpow := enn_pair_le hQ _ _ _ hsum
    have e : ENNReal.ofReal ((a / 2) ^ Q) = ENNReal.ofReal (a / 2) ^ Q := by
      rw [ENNReal.ofReal_rpow_of_nonneg ha2 (by linarith)]
    rw [e]
    exact hpow
  have hL := lintegral_pair_lower hQ hum ht ht4 hκ0nn hpt'
  set K : ℝ := (a / 2) ^ Q * (t / 4) / 2 ^ (Q - 1) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have : (0 : ℝ) < 2 ^ (Q - 1) := by positivity
    exact div_nonneg (mul_nonneg hκ0nn (by linarith)) this.le
  have hP : (2 : ℝ≥0∞) ^ (Q - 1) = ENNReal.ofReal (2 ^ (Q - 1)) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
      ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]
  have hPpos : (2 : ℝ≥0∞) ^ (Q - 1) ≠ 0 := by
    rw [hP]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hPtop : (2 : ℝ≥0∞) ^ (Q - 1) ≠ ⊤ := by
    rw [hP]; exact ENNReal.ofReal_ne_top
  have hKP : ENNReal.ofReal K * (2 : ℝ≥0∞) ^ (Q - 1) = ENNReal.ofReal ((a / 2) ^ Q * (t / 4)) := by
    rw [hP, ← ENNReal.ofReal_mul hK0]
    congr 1
    have : (0 : ℝ) < 2 ^ (Q - 1) := by positivity
    rw [hK]; field_simp
  have hEK : ENNReal.ofReal K ≤ ∫⁻ y in Icc (0 : ℝ) 1, ‖(fun x => bumpS φB a (1 / 4) t x - g x) y‖ₑ ^ Q := by
    apply (ENNReal.mul_le_mul_left hPpos hPtop).mp
    calc (2 : ℝ≥0∞) ^ (Q - 1) * ENNReal.ofReal K = ENNReal.ofReal K * (2 : ℝ≥0∞) ^ (Q - 1) :=
          mul_comm _ _
      _ = ENNReal.ofReal ((a / 2) ^ Q * (t / 4)) := hKP
      _ ≤ _ := hL
  have hfin := eLpNorm_ge_of_lintegral hp0 hpt hK0 hEK
  have hval : K ^ Q⁻¹ = a * t ^ Q⁻¹ * cpConst Q := by
    have hc : (0 : ℝ) ≤ 1 / (4 * 2 ^ (Q - 1)) := by positivity
    have hsplit : K = (a / 2) ^ Q * (t * (1 / (4 * 2 ^ (Q - 1)))) := by
      rw [hK]; ring
    rw [hsplit, Real.mul_rpow hκ0nn (mul_nonneg ht.le hc), Real.mul_rpow ht.le hc,
      Real.rpow_rpow_inv ha2 hQ0, cpConst]
    ring
  show ENNReal.ofReal (a * t ^ Q⁻¹ * cpConst Q) ≤
    eLpNorm (bumpS φB a (1 / 4) t - g) p (volume.restrict (Icc (0 : ℝ) 1))
  rw [← hval]
  exact hfin

/-! ## Piso de inclinação na biblioteca -/

/-- Membros de `Σ_N^H` são `H`-Lipschitz em `[0,1]` (zero, ou elementos de `classNH`). -/
lemma sigma_lipschitz {H N : ℕ} {g : ℝ → ℝ} (hg : g ∈ Pendencias.Agenda.Sigma (fun _ => H) N) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |g x - g y| ≤ (H : ℝ) * |x - y| := by
  have hcl : g ∈ FormalizacaoLp.classNH N H ∨ g = 0 := by
    simp only [Pendencias.Agenda.Sigma, Set.mem_setOf_eq] at hg
    rcases hg with h0 | ⟨T, hadm, hT⟩
    · exact Or.inr h0
    · exact Or.inl ⟨T, hadm, hT⟩
  rcases hcl with hc | rfl
  · exact fun x hx y hy => FormalizacaoAltura.classNH_lipschitz hc hx hy
  · intro x _ y _
    simp only [Pi.zero_apply, sub_self, abs_zero]
    positivity

/-- **Piso de inclinação em toda a biblioteca.** Para `0 < s ≤ 1/p`, com `δ = 1/p - s` e
`β = s/(1+δ)`, existe `f_H` na bola unitária de Besov com `dist_{L^p}(f_H, g) ≥ c_L H^{-β}`
para todo `g ∈ Σ_N^H` e todo `N`. -/
theorem slope_floor {p q : ℝ≥0∞} {s : ℝ} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hq0 : 0 < q)
    (hs : 0 < s) (hs2 : s < 2) (hsp : s ≤ p.toReal⁻¹) :
    ∃ c : ℝ, 0 < c ∧ ∀ H : ℕ, 2 ≤ H → ∃ f : ℝ → ℝ, Measurable f ∧ besovNorm p s q f ≤ 1 ∧
      ∀ N : ℕ, ∀ g ∈ Pendencias.Agenda.Sigma (fun _ => H) N,
        ENNReal.ofReal (c * (H : ℝ) ^ (-(s / (1 + (p.toReal⁻¹ - s))))) ≤ distP p f g := by
  obtain ⟨M, hM, hbd⟩ := exists_M_φB
  obtain ⟨Λ, hΛ0, hΛ⟩ := besovNorm_bumpS_le hp1 hpt hq0 hs hs2 (φ := φB)
    (fun z hz => φB_zero_of_not_Ioo hz) (C0 := 1) φB_abs_le zero_le_one φB_diff deriv_φB_diff
    hbd hM.le
  set Λ' : ℝ := max Λ 1 with hΛ'
  have hΛ'pos : 0 < Λ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΛΛ' : Λ ≤ Λ' := le_max_left _ _
  set δ : ℝ := p.toReal⁻¹ - s with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have h1δ : 0 < 1 + δ := by linarith
  set cc : ℝ := min (1 / Λ') (2 * (4 : ℝ) ^ (-(1 + δ))) with hcc
  have hcc0 : 0 < cc := lt_min (by positivity) (by positivity)
  have hccΛ : cc ≤ 1 / Λ' := min_le_left _ _
  have hcc4 : cc ≤ 2 * (4 : ℝ) ^ (-(1 + δ)) := min_le_right _ _
  set β : ℝ := s / (1 + δ) with hβ
  refine ⟨cc * cpConst p.toReal * (cc / 2) ^ β, by unfold cpConst; positivity, fun H hH => ?_⟩
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
  set t : ℝ := (cc / (2 * (H : ℝ))) ^ ((1 + δ)⁻¹) with ht_def
  have ht : 0 < t := by positivity
  have htpow : t ^ (1 + δ) = cc / (2 * (H : ℝ)) := by
    rw [ht_def]; exact Real.rpow_inv_rpow (by positivity) h1δ.ne'
  have ht4 : t ≤ 1 / 4 := by
    have hle : t ^ (1 + δ) ≤ (1 / 4) ^ (1 + δ) := by
      rw [htpow]
      have h4 : (1 / 4 : ℝ) ^ (1 + δ) = (4 : ℝ) ^ (-(1 + δ)) := by
        rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
      rw [h4]
      have hb : (2 : ℝ) * (4 : ℝ) ^ (-(1 + δ)) / (2 * (H : ℝ)) ≤ (4 : ℝ) ^ (-(1 + δ)) := by
        rw [div_le_iff₀ (by positivity)]
        have : (0 : ℝ) < (4 : ℝ) ^ (-(1 + δ)) := by positivity
        nlinarith
      calc cc / (2 * (H : ℝ)) ≤ (2 * (4 : ℝ) ^ (-(1 + δ))) / (2 * (H : ℝ)) :=
            div_le_div_of_nonneg_right hcc4 (by positivity)
        _ ≤ (4 : ℝ) ^ (-(1 + δ)) := hb
    exact (Real.rpow_le_rpow_iff ht.le (by norm_num) h1δ).mp hle
  set a : ℝ := cc * t ^ (-δ) with ha_def
  have ha : 0 ≤ a := by positivity
  have hHt : H * t = a / 2 := by
    have hpos : 0 < t ^ δ := Real.rpow_pos_of_pos ht δ
    have hsplit : t ^ (1 + δ) = t * t ^ δ := by
      rw [Real.rpow_add ht, Real.rpow_one]
    have hH' : (H : ℝ) * t * t ^ δ = cc / 2 := by
      have e2 : (H : ℝ) * t * t ^ δ = (H : ℝ) * (t * t ^ δ) := by ring
      rw [e2, ← hsplit, htpow]
      field_simp
    have hq : (H : ℝ) * t = (cc / 2) / t ^ δ := by
      rw [eq_div_iff hpos.ne']; linarith [hH']
    rw [hq, ha_def, Real.rpow_neg ht.le]
    ring
  refine ⟨bumpS φB a (1 / 4) t, ?_, ?_, ?_⟩
  · have hc : Continuous (bumpS φB a (1 / 4) t) := by
      unfold bumpS
      exact continuous_const.mul (φB_smooth.continuous.comp
        ((continuous_id.sub continuous_const).div_const t))
    exact hc.measurable
  · -- norma de Besov unitária
    refine (hΛ a (1 / 4) t ht (by linarith)).trans ?_
    apply ENNReal.ofReal_le_one.mpr
    have hprod : Λ * |a| * t ^ (p.toReal⁻¹ - s) = Λ * cc := by
      rw [abs_of_nonneg ha, ha_def, ← hδ]
      have : t ^ (-δ) * t ^ δ = 1 := by
        rw [← Real.rpow_add ht]; norm_num
      calc Λ * (cc * t ^ (-δ)) * t ^ δ = Λ * cc * (t ^ (-δ) * t ^ δ) := by ring
        _ = Λ * cc := by rw [this, mul_one]
    rw [hprod]
    have hΛcc : Λ * cc ≤ 1 := by
      calc Λ * cc ≤ Λ' * (1 / Λ') := mul_le_mul hΛΛ' hccΛ hcc0.le (by linarith)
        _ = 1 := by field_simp
    exact hΛcc
  · intro N g hg
    have hdist := slope_dist_lower hp1 hpt (H := (H : ℝ)) (measurable_sigma hg)
      (sigma_lipschitz hg) ha ht ht4 (le_of_eq hHt)
    refine le_trans (le_of_eq ?_) hdist
    congr 1
    have hx : t ^ (-δ) * t ^ (p.toReal⁻¹) = t ^ s := by
      rw [← Real.rpow_add ht]; congr 1; rw [hδ]; ring
    have hts : t ^ s = (cc / 2) ^ β * (H : ℝ) ^ (-β) := by
      rw [ht_def, ← Real.rpow_mul (by positivity), show (1 + δ)⁻¹ * s = β by rw [hβ]; ring]
      rw [show cc / (2 * (H : ℝ)) = (cc / 2) * (H : ℝ)⁻¹ by field_simp,
        Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hHpos.le,
        Real.rpow_neg hHpos.le]
    have key : t ^ p.toReal⁻¹ * t ^ (-δ) = (cc / 2) ^ β * (H : ℝ) ^ (-β) := by
      rw [mul_comm, hx, hts]
    rw [ha_def]
    calc cc * cpConst p.toReal * (cc / 2) ^ β * (H : ℝ) ^ (-β)
        = cc * cpConst p.toReal * ((cc / 2) ^ β * (H : ℝ) ^ (-β)) := by ring
      _ = cc * cpConst p.toReal * (t ^ p.toReal⁻¹ * t ^ (-δ)) := by rw [key]
      _ = cc * t ^ (-δ) * t ^ p.toReal⁻¹ * cpConst p.toReal := by ring


end FormalizacaoAltura
