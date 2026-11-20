import Formalizacao.Lemma55b

/-!
# Lema 5.5 (M6), parte (a): limite uniforme das escalas e cota sup

`F r = Q_{2^{r+1}} f`. Pelas cotas de `Lemma55b`, `|F (k+1) - F k| ≤ K q^{k+1}` em `[0,1]`, com
`q = 2^{-(s-1/p)} < 1`. Daí `F` é uniformemente de Cauchy em `[0,1]`; o limite `G` é contínuo,
com `|G| ≤ |F 0| + K q/(1-q)`.
-/

open scoped ENNReal
open Filter Topology
open MeasureTheory Set FormalizacaoLp FormalizacaoGrid FormalizacaoL55 FormalizacaoL55b

namespace FormalizacaoL55c

/-- A sequência `F r = Q_{2^{r+1}} f`. -/
noncomputable def F (f : ℝ → ℝ) (r : ℕ) : ℝ → ℝ := fun x => Q (2 ^ (r + 1)) f x

/-- A razão geométrica `q = (2^{s-1/p})^{-1}`. -/
noncomputable def qr (p s : ℝ) : ℝ := ((2 : ℝ) ^ (s - 1 / p))⁻¹

lemma qr_nonneg (p s : ℝ) : 0 ≤ qr p s := by unfold qr; positivity

lemma qr_lt_one {p s : ℝ} (hs : 1 / p < s) : qr p s < 1 := by
  unfold qr
  have h1 : (1 : ℝ) < (2 : ℝ) ^ (s - 1 / p) := Real.one_lt_rpow (by norm_num) (by linarith)
  exact inv_lt_one_of_one_lt₀ h1

/-- `(2^{k s'})^{-1} = q^k`. -/
lemma inv_rpow_mul_eq_qr_pow (p s : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ ((k : ℝ) * (s - 1 / p)))⁻¹ = qr p s ^ k := by
  unfold qr
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]

/-- Cota de passo: `|F (k+1) x - F k x| ≤ K q^{k+1}` em `[0,1]`. -/
theorem diff_step {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (k : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |F f (k + 1) x - F f k x| ≤ 144 * CW * S.toReal * (2 : ℝ) ^ (1 / p) * qr p s ^ (k + 1) := by
  have h := vk_sup_le hp hW hCW hf hfi hfin hS hbS (k := k + 1) (by omega) hx
  rw [inv_rpow_mul_eq_qr_pow] at h
  exact h

/-- Constante `K = 144 C_W S 2^{1/p}`. -/
noncomputable def Kc (p CW : ℝ) (S : ℝ≥0∞) : ℝ := 144 * CW * S.toReal * (2 : ℝ) ^ (1 / p)

lemma Kc_nonneg {p CW : ℝ} (hCW : 0 ≤ CW) (S : ℝ≥0∞) : 0 ≤ Kc p CW S := by
  unfold Kc; positivity

/-- Soma telescópica com cota geométrica: `|F (a+d) x - F a x| ≤ K q^{a+1}/(1-q)`. -/
theorem diff_from {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (a d : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |F f (a + d) x - F f a x| ≤ Kc p CW S * qr p s ^ (a + 1) / (1 - qr p s) := by
  have hq1 := qr_lt_one (p := p) hs
  have hq0 := qr_nonneg p s
  have hsum : ∀ d : ℕ, |F f (a + d) x - F f a x| ≤
      ∑ i ∈ Finset.range d, Kc p CW S * qr p s ^ (a + i + 1) := by
    intro d
    induction d with
    | zero => simp [F]
    | succ d ih =>
      have h1 := diff_step hp hW hCW hf hfi hfin hS hbS (a + d) hx
      have htri : |F f (a + (d + 1)) x - F f a x| ≤
          |F f (a + d + 1) x - F f (a + d) x| + |F f (a + d) x - F f a x| := by
        have : F f (a + (d + 1)) x - F f a x =
            (F f (a + d + 1) x - F f (a + d) x) + (F f (a + d) x - F f a x) := by
          rw [show a + (d + 1) = a + d + 1 by ring]; ring
        rw [this]
        exact abs_add_le _ _
      rw [Finset.sum_range_succ]
      have e1 : Kc p CW S * qr p s ^ (a + d + 1) = 144 * CW * S.toReal * (2 : ℝ) ^ (1 / p) * qr p s ^ (a + d + 1) := rfl
      calc |F f (a + (d + 1)) x - F f a x|
          ≤ |F f (a + d + 1) x - F f (a + d) x| + |F f (a + d) x - F f a x| := htri
        _ ≤ Kc p CW S * qr p s ^ (a + d + 1) + ∑ i ∈ Finset.range d, Kc p CW S * qr p s ^ (a + i + 1) := by
            apply add_le_add
            · rw [e1]; exact h1
            · exact ih
        _ = ∑ i ∈ Finset.range d, Kc p CW S * qr p s ^ (a + i + 1) + Kc p CW S * qr p s ^ (a + d + 1) := by
            ring
  refine (hsum d).trans ?_
  have hgeom : ∑ i ∈ Finset.range d, qr p s ^ i ≤ 1 / (1 - qr p s) := by
    have := geom_sum_Ico_le_of_lt_one (x := qr p s) (m := 0) (n := d) hq0 hq1
    rw [Finset.range_eq_Ico]
    simpa using this
  have hrew : ∑ i ∈ Finset.range d, Kc p CW S * qr p s ^ (a + i + 1) =
      Kc p CW S * qr p s ^ (a + 1) * ∑ i ∈ Finset.range d, qr p s ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hrew]
  have hK := Kc_nonneg (p := p) hCW S
  have hpow : 0 ≤ Kc p CW S * qr p s ^ (a + 1) := mul_nonneg hK (pow_nonneg hq0 _)
  calc Kc p CW S * qr p s ^ (a + 1) * ∑ i ∈ Finset.range d, qr p s ^ i
      ≤ Kc p CW S * qr p s ^ (a + 1) * (1 / (1 - qr p s)) := mul_le_mul_of_nonneg_left hgeom hpow
    _ = Kc p CW S * qr p s ^ (a + 1) / (1 - qr p s) := by ring

/-- Cota triangular: `Np(Q_n f) ≤ Np f + Np(f - Q_n f)`. -/
theorem Np_Q_le {p : ℝ} (hp : 1 ≤ p) {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f) :
    Np p (Q n f) (Icc 0 1) ≤ Np p f (Icc 0 1) + Np p (fun x => f x - Q n f x) (Icc 0 1) := by
  have hfun : Q n f = fun x => f x + -(f x - Q n f x) := by funext x; ring
  have hm : Measurable fun x => f x - Q n f x := hf.sub (Q_continuous n f).measurable
  unfold Np at *
  conv_lhs => rw [hfun]
  calc eLpNorm (fun x => f x + -(f x - Q n f x)) (ENNReal.ofReal p) (volume.restrict (Icc 0 1))
      ≤ eLpNorm f (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) +
          eLpNorm (fun x => -(f x - Q n f x)) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) :=
        eLpNorm_add_le hf.aestronglyMeasurable hm.neg.aestronglyMeasurable
          (ENNReal.one_le_ofReal.2 hp)
    _ = eLpNorm f (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) +
          eLpNorm (fun x => f x - Q n f x) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) := by
        congr 1
        exact eLpNorm_neg (fun x => f x - Q n f x) _ _

/-- Cota sup de `F 0 = Q_2 f`, em `[0,1]`. -/
theorem F0_bound {p CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |F f 0 x| ≤ 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) *
      (Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal := by
  have hq2 : F f 0 = Q 2 f := by
    funext y; unfold F; norm_num
  rw [hq2]
  have hpos := Np_Q_le (n := 2) hp hf
  have hd := FormalizacaoCor.quasi_error hp hW (show 2 ≤ 2 by norm_num) hf hfi hfin
  have hω : wtP (ENNReal.ofReal p) (1 / ((2 : ℕ) : ℝ)) f < ⊤ := by
    have := wtP_lt_top hp hf hfin 2
    simpa using this
  have hsum_fin : Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨hfin.ne, ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) ?_⟩
    simpa using hω.ne
  have hQ : Np p (Q 2 f) (Icc 0 1) ≠ ⊤ := ne_top_of_le_ne_top hsum_fin
    (le_trans hpos (add_le_add le_rfl (by simpa using hd)))
  have hbd : (Np p (Q 2 f) (Icc 0 1)).toReal ≤ (Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal :=
    ENNReal.toReal_mono hsum_fin (le_trans hpos (add_le_add le_rfl (by simpa using hd)))
  have hs := sup_le_of_affine_cells (N := 2) hp (le_refl 2)
    (fun j hj => by
      obtain ⟨a, b, h⟩ := Q_affine_on_cell (n := 2) (by norm_num) hj f
      exact ⟨a, b, h⟩)
    (lt_top_iff_ne_top.2 hQ) hx
  refine hs.trans ?_
  have hc : (0 : ℝ) ≤ 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) := by positivity
  exact mul_le_mul_of_nonneg_left hbd hc

/-- Sequência uniformemente de Cauchy em `[0,1]`. -/
theorem unif_cauchy {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) :
    UniformCauchySeqOn (fun r => F f r) atTop (Icc (0 : ℝ) 1) := by
  have hq1 := qr_lt_one (p := p) hs
  have hq0 := qr_nonneg p s
  set c : ℝ := Kc p CW S / (1 - qr p s) with hc
  have hc0 : 0 ≤ c := div_nonneg (Kc_nonneg hCW S) (by linarith)
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (c + 1) by positivity) hq1
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  -- para `m ≤ n`: |F n - F m| ≤ c q^{m+1} ≤ c q^N < ε
  have key : ∀ a b : ℕ, N ≤ a → a ≤ b → |F f b x - F f a x| < ε := by
    intro a b ha hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    have h1 := diff_from hp hW hCW hf hfi hfin hS hbS hs a d hx
    have h2 : Kc p CW S * qr p s ^ (a + 1) / (1 - qr p s) = c * qr p s ^ (a + 1) := by
      rw [hc]; ring
    rw [h2] at h1
    have hpow : qr p s ^ (a + 1) ≤ qr p s ^ N := pow_le_pow_of_le_one hq0 hq1.le (by omega)
    have h3 : c * qr p s ^ (a + 1) ≤ c * qr p s ^ N := mul_le_mul_of_nonneg_left hpow hc0
    have h4 : c * qr p s ^ N < ε := by
      have : c * qr p s ^ N ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hN.le hc0
      have h5 : c * (ε / (c + 1)) < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    have : |F f (a + d) x - F f a x| < ε := lt_of_le_of_lt (h1.trans h3) h4
    exact this
  rcases le_total m n with hmn | hmn
  · have := key m n hm hmn
    rw [Real.dist_eq, abs_sub_comm]
    exact this
  · have := key n m hn hmn
    rw [Real.dist_eq]
    exact this

/-- Limite pontual `G` das escalas `F r` em `[0,1]`. -/
noncomputable def Glim (f : ℝ → ℝ) (x : ℝ) : ℝ := limUnder atTop (fun r => F f r x)

theorem tendsto_Glim {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun r => F f r x) atTop (𝓝 (Glim f x)) := by
  have hunif := unif_cauchy hp hW hCW hf hfi hfin hS hbS hs
  have hc : CauchySeq (fun r => F f r x) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.1 hunif) ε hε
    exact ⟨N, fun n hn => hN n hn N le_rfl x hx⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  exact tendsto_nhds_limUnder ⟨L, hL⟩

/-- **Parte (a), continuidade e cota sup.** O limite `G` é contínuo em `[0,1]` e
`|G x| ≤ |F_0 x| + K q/(1-q)`. -/
theorem Glim_continuousOn {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW)
    (hCW : 0 ≤ CW) {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) :
    ContinuousOn (Glim f) (Icc 0 1) := by
  have hunif := unif_cauchy hp hW hCW hf hfi hfin hS hbS hs
  have hlim : TendstoUniformlyOn (fun r => F f r) (Glim f) atTop (Icc (0 : ℝ) 1) :=
    UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto hunif
      (fun x hx => tendsto_Glim hp hW hCW hf hfi hfin hS hbS hs hx)
  exact hlim.continuousOn (Eventually.of_forall fun r => (Q_continuous (2 ^ (r + 1)) f).continuousOn).frequently

/-- Cota sup: `|G x| ≤ B_0 + K q/(1-q)` em `[0,1]`, com `B_0` o da primeira escala. -/
theorem Glim_bound {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW)
    (hCW : 0 ≤ CW) {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |Glim f x| ≤ 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) *
        (Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal +
      Kc p CW S * qr p s ^ (0 + 1) / (1 - qr p s) := by
  have hbound : ∀ r : ℕ, |F f r x - F f 0 x| ≤ Kc p CW S * qr p s ^ (0 + 1) / (1 - qr p s) := by
    intro r
    have := diff_from hp hW hCW hf hfi hfin hS hbS hs 0 r hx
    rw [zero_add] at this
    exact this
  have hlimabs : |Glim f x - F f 0 x| ≤ Kc p CW S * qr p s ^ (0 + 1) / (1 - qr p s) := by
    have ht : Tendsto (fun r => |F f r x - F f 0 x|) atTop (𝓝 |Glim f x - F f 0 x|) :=
      ((tendsto_Glim hp hW hCW hf hfi hfin hS hbS hs hx).sub_const (F f 0 x)).abs
    exact le_of_tendsto ht (Eventually.of_forall hbound)
  have h0 := F0_bound hp hW hCW hf hfi hfin hx
  calc |Glim f x| = |(Glim f x - F f 0 x) + F f 0 x| := by ring_nf
    _ ≤ |Glim f x - F f 0 x| + |F f 0 x| := abs_add_le _ _
    _ ≤ Kc p CW S * qr p s ^ (0 + 1) / (1 - qr p s) + 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) *
        (Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal :=
        add_le_add hlimabs h0
    _ = _ := by ring

/-- `|G x - F_r x| ≤ c q^{r+1}` em `[0,1]` (passagem ao limite na cota telescópica). -/
theorem Glim_sub_le {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (r : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |Glim f x - F f r x| ≤ Kc p CW S * qr p s ^ (r + 1) / (1 - qr p s) := by
  have hbound : ∀ m : ℕ, |F f (r + m) x - F f r x| ≤ Kc p CW S * qr p s ^ (r + 1) / (1 - qr p s) :=
    fun m => diff_from hp hW hCW hf hfi hfin hS hbS hs r m hx
  have ht : Tendsto (fun m : ℕ => |F f (r + m) x - F f r x|) atTop (𝓝 |Glim f x - F f r x|) := by
    have hT : Tendsto (fun m : ℕ => F f (r + m) x) atTop (𝓝 (Glim f x)) := by
      refine (tendsto_Glim hp hW hCW hf hfi hfin hS hbS hs hx).comp ?_
      simpa only [add_comm] using tendsto_add_atTop_nat r
    exact ((hT.sub_const (F f r x)).abs)
  exact le_of_tendsto ht (Eventually.of_forall hbound)

/-- Cota L^p de `f - F_r` em `[0,1]`, por Cor. 5.4: `Np(f - F_r) ≤ 9 C_W ω_p(f, 1/2^{r+1})`. -/
theorem Np_f_sub_F_le {p CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) (r : ℕ) :
    Np p (fun x => f x - F f r x) (Icc 0 1) ≤
      9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / ((2 ^ (r + 1) : ℕ) : ℝ)) f := by
  have h := FormalizacaoCor.quasi_error hp hW (show 2 ≤ 2 ^ (r + 1) from by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) hf hfi hfin
  exact h

/-- `f = G` quase certamente em `[0,1]`. -/
theorem ae_eq_Glim {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), f x = Glim f x := by
  have hq1 := qr_lt_one (p := p) hs
  have hq0 := qr_nonneg p s
  have hSnn : 0 ≤ S.toReal := ENNReal.toReal_nonneg
  have hpos : (0 : ℝ) < p := by linarith
  -- majorante real
  set g : ℕ → ℝ := fun r => 9 * CW * S.toReal * ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s))⁻¹ +
    Kc p CW S * qr p s ^ (r + 1) / (1 - qr p s) with hg
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℕ => ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s))⁻¹) atTop (𝓝 0) := by
      have hs0 : 0 < s := by
        have : (0 : ℝ) < 1 / p := by positivity
        linarith
      have hb : Tendsto (fun r : ℕ => (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s)) atTop atTop := by
        have hr : (1 : ℝ) < (2 : ℝ) ^ s := Real.one_lt_rpow (by norm_num) hs0
        have heq : (fun r : ℕ => (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s)) =
            fun r : ℕ => ((2 : ℝ) ^ s) ^ (r + 1) := by
          funext r
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          push_cast
          ring_nf
        rw [heq]
        exact (tendsto_pow_atTop_atTop_of_one_lt hr).comp (tendsto_add_atTop_nat 1)
      exact tendsto_inv_atTop_zero.comp hb
    have h2 : Tendsto (fun r : ℕ => qr p s ^ (r + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp (tendsto_add_atTop_nat 1)
    have h3 := ((h1.const_mul (9 * CW * S.toReal)).add
      (h2.const_mul (Kc p CW S / (1 - qr p s))))
    simp only [mul_zero, add_zero] at h3
    convert h3 using 2 with r
    rw [hg]; ring
  -- cota de `Np(f - G)` por `ofReal (g r)` para todo `r`
  have hbound : ∀ r : ℕ, Np p (fun x => f x - Glim f x) (Icc 0 1) ≤ ENNReal.ofReal (g r) := by
    intro r
    have hfun : (fun x => f x - Glim f x) = fun x => (f x - F f r x) + (F f r x - Glim f x) := by
      funext x; ring
    have hm1 : Measurable fun x => f x - F f r x := hf.sub (Q_continuous _ f).measurable
    have hm2 : AEStronglyMeasurable (fun x => F f r x - Glim f x) (volume.restrict (Icc 0 1)) := by
      apply AEStronglyMeasurable.sub
      · exact (Q_continuous _ f).aestronglyMeasurable
      · exact (Glim_continuousOn hp hW hCW hf hfi hfin hS hbS hs).aestronglyMeasurable measurableSet_Icc
    set h : ℝ := ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s))⁻¹ with hh
    have hhnn : 0 ≤ h := inv_nonneg.2 (Real.rpow_nonneg (by norm_num) _)
    have hA := Np_f_sub_F_le hp hW hf hfi hfin r
    have hωr : wtP (ENNReal.ofReal p) (1 / ((2 ^ (r + 1) : ℕ) : ℝ)) f ≤
        ENNReal.ofReal (S.toReal * h) := by
      have hW' := Wr_le_of_besov (p := p) (s := s) hS hbS (r + 1)
      have hfin' : wtP (ENNReal.ofReal p) (1 / ((2 ^ (r + 1) : ℕ) : ℝ)) f ≠ ⊤ := by
        have := wtP_lt_top hp hf hfin (2 ^ (r + 1))
        exact this.ne
      rw [ENNReal.le_ofReal_iff_toReal_le hfin' (mul_nonneg hSnn hhnn)]
      exact hW'
    have hA' : Np p (fun x => f x - F f r x) (Icc 0 1) ≤
        ENNReal.ofReal (9 * CW * S.toReal * h) := by
      refine hA.trans ?_
      have hc9 : ENNReal.ofReal (9 * CW * S.toReal * h) =
          ENNReal.ofReal 9 * ENNReal.ofReal CW * ENNReal.ofReal (S.toReal * h) := by
        have e : 9 * CW * S.toReal * h = (9 * CW) * (S.toReal * h) := by ring
        rw [e, ENNReal.ofReal_mul (mul_nonneg (by norm_num) hCW),
          ENNReal.ofReal_mul (by norm_num)]
      rw [hc9, ENNReal.ofReal_ofNat]
      calc 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / ((2 ^ (r + 1) : ℕ) : ℝ)) f
          = 9 * (ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / ((2 ^ (r + 1) : ℕ) : ℝ)) f) := by ring
        _ ≤ 9 * (ENNReal.ofReal CW * ENNReal.ofReal (S.toReal * h)) :=
            mul_le_mul_left' (mul_le_mul_left' hωr _) _
        _ = 9 * ENNReal.ofReal CW * ENNReal.ofReal (S.toReal * h) := by ring
    have hB : Np p (fun x => F f r x - Glim f x) (Icc 0 1) ≤ ENNReal.ofReal (Kc p CW S * qr p s ^ (r + 1) / (1 - qr p s)) := by
      unfold Np
      refine (eLpNorm_le_of_ae_bound (C := Kc p CW S * qr p s ^ (r + 1) / (1 - qr p s)) ?_).trans ?_
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact Glim_sub_le hp hW hCW hf hfi hfin hS hbS hs r hx
      · rw [Measure.restrict_apply_univ, Real.volume_Icc]
        simp
    rw [hfun]
    calc eLpNorm (fun x => (f x - F f r x) + (F f r x - Glim f x)) (ENNReal.ofReal p) (volume.restrict (Icc 0 1))
        ≤ eLpNorm (fun x => f x - F f r x) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) +
          eLpNorm (fun x => F f r x - Glim f x) (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) :=
          eLpNorm_add_le hm1.aestronglyMeasurable hm2 (ENNReal.one_le_ofReal.2 hp)
      _ ≤ ENNReal.ofReal (9 * CW * S.toReal * ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s))⁻¹) +
          ENNReal.ofReal (Kc p CW S * qr p s ^ (r + 1) / (1 - qr p s)) := add_le_add hA' hB
      _ = ENNReal.ofReal (g r) := by
          have hn1 : 0 ≤ 9 * CW * S.toReal * h := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCW) hSnn) hhnn
          have hn2 : 0 ≤ Kc p CW S * qr p s ^ (r + 1) / (1 - qr p s) :=
            div_nonneg (mul_nonneg (Kc_nonneg hCW S) (pow_nonneg hq0 _)) (by linarith)
          rw [← ENNReal.ofReal_add hn1 hn2]
  have hlim : Tendsto (fun r : ℕ => ENNReal.ofReal (g r)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hg0
    simpa using this
  have hzero : Np p (fun x => f x - Glim f x) (Icc 0 1) = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) (zero_le _)
  have hae : (fun x => f x - Glim f x) =ᵐ[volume.restrict (Icc 0 1)] 0 := by
    unfold Np at hzero
    have hm : AEStronglyMeasurable (fun x => f x - Glim f x) (volume.restrict (Icc 0 1)) := by
      apply AEStronglyMeasurable.sub
      · exact hf.aestronglyMeasurable
      · exact (Glim_continuousOn hp hW hCW hf hfi hfin hS hbS hs).aestronglyMeasurable measurableSet_Icc
    exact (eLpNorm_eq_zero_iff hm (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)).1 hzero
  filter_upwards [hae] with x hx
  have : f x - Glim f x = 0 := hx
  linarith

end FormalizacaoL55c
