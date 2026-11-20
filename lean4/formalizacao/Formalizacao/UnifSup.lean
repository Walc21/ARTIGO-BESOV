import Formalizacao.LowSup
import Formalizacao.UnifLq

/-!
# Seção 6, parte 2: cota em sup uniforme sobre bolas (`Lema lp:lem:uniform-height (b)`)

`lam_bound_unif`: para `f` na bola `besovNorm p s q f ≤ B` e `r ≥ 1`, `|λ_j(f)| ≤ C B Λ_r`, com
`C = C(p,s,q)` independente de `B` e de `f`, e `Λ_r = 1` (`s > 1/p`), `2^{r(1/p-s)}`
(`s < 1/p`) ou `r^{θ_q}` (`s = 1/p`).

A prova refaz `lam_bound` rastreando as constantes: a série telescópica `Q_sup_le` é linear em
`‖f‖_p`, `ω_p(f,1/2)` e na sequência de Besov, todas limitadas por `B`. Para `s > 1/p` a mesma
série basta (razão `2^{1/p-s} < 1`), sem passar pelo representante contínuo.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid FormalizacaoLp FormalizacaoL55 FormalizacaoL55b
  FormalizacaoL55c FormalizacaoRed

namespace FormalizacaoLow

/-- Norma de Besov `‖f‖*_{B^s_{p,q}} = ‖f‖_p + ‖(2^{rs} ω_p(f,2^{-r}))_r‖_{ℓ^q}` em `ℝ≥0∞`. -/
noncomputable def besovNorm (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) (f : ℝ → ℝ) : ℝ≥0∞ :=
  eLpNorm f p vol01 + lqNorm q (besovSeq p s f)

/-- Fator de crescimento uniforme: `1` para `s > 1/p`, e `Λ_r` de `Lam` nos demais casos. -/
noncomputable def LamU (p s : ℝ) (q : ℝ≥0∞) (r : ℕ) : ℝ :=
  if 1 / p < s then 1 else Lam p s q r

lemma one_le_LamU (p s : ℝ) (q : ℝ≥0∞) {r : ℕ} (hr : 1 ≤ r) : 1 ≤ LamU p s q r := by
  unfold LamU
  split_ifs with h
  · exact le_rfl
  · exact one_le_Lam p s q hr (not_lt.1 h)

lemma lqNorm_le_besovNorm (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) (f : ℝ → ℝ) :
    lqNorm q (besovSeq p s f) ≤ besovNorm p s q f := le_add_self

lemma eLpNorm_le_besovNorm (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) (f : ℝ → ℝ) :
    eLpNorm f p vol01 ≤ besovNorm p s q f := le_self_add

/-- Em uma bola de raio `B`, as quantidades de base são limitadas por `B`. -/
lemma ball_bounds {p : ℝ} (hp : 1 ≤ p) {s : ℝ} {q : ℝ≥0∞} (hq : 0 < q) {B : ℝ} (hB : 0 ≤ B)
    {f : ℝ → ℝ} (hf : Measurable f)
    (hball : besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B) :
    (Np p f (Icc 0 1)).toReal ≤ B ∧
    (⨆ r, besovSeq (ENNReal.ofReal p) s f r).toReal ≤ B ∧
    (lqNorm q (besovSeq (ENNReal.ofReal p) s f)).toReal ≤ B ∧
    Np p f (Icc 0 1) < ⊤ ∧ (⨆ r, besovSeq (ENNReal.ofReal p) s f r) < ⊤ ∧
    lqNorm q (besovSeq (ENNReal.ofReal p) s f) < ⊤ := by
  have h1 : Np p f (Icc 0 1) ≤ ENNReal.ofReal B :=
    (eLpNorm_le_besovNorm _ s q f).trans hball
  have h2 : lqNorm q (besovSeq (ENNReal.ofReal p) s f) ≤ ENNReal.ofReal B :=
    (lqNorm_le_besovNorm _ s q f).trans hball
  have h3 : (⨆ r, besovSeq (ENNReal.ofReal p) s f r) ≤ ENNReal.ofReal B :=
    (FormalizacaoLq.iSup_le_lq hq _).trans h2
  have hf1 : Np p f (Icc 0 1) < ⊤ := lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
  refine ⟨?_, ?_, ?_, hf1, lt_of_le_of_lt h3 ENNReal.ofReal_lt_top,
    lt_of_le_of_lt h2 ENNReal.ofReal_lt_top⟩
  · have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal hB] at this
  · have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
    rwa [ENNReal.toReal_ofReal hB] at this
  · have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_ofReal hB] at this

/-- Cota telescópica com constantes explícitas na bola. -/
lemma lam_le_B0_sum {p CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) (r : ℕ) (hr : 1 ≤ r) (j : ℕ) (hj : j ≤ 2 ^ r) :
    |lam (2 ^ r) f j| ≤ B0 p CW f + ∑ k ∈ Finset.Ico 1 r,
      144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) := by
  have hn : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rw [← FormalizacaoJ.Q_node hn f hj]
  exact Q_sup_le hp hW hCW hf hfi hfin (tn_mem_Icc hn hj) r hr

/-- `B0 ≤ b0 · B` na bola. -/
lemma B0_le_ball {p CW : ℝ} (hp : 1 ≤ p) (hCW : 0 ≤ CW) {B : ℝ} (hB : 0 ≤ B)
    {f : ℝ → ℝ} (hf : Measurable f) (hNp : (Np p f (Icc 0 1)).toReal ≤ B)
    (hfin : Np p f (Icc 0 1) < ⊤) :
    B0 p CW f ≤ (8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW)) * B := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hw : wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f ≤ 4 * Np p f (Icc 0 1) :=
    wtP_le_four hp1 _ hf
  have hsum : Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f ≤
      ENNReal.ofReal (1 + 36 * CW) * Np p f (Icc 0 1) := by
    calc Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f
        ≤ Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * (4 * Np p f (Icc 0 1)) := by gcongr
      _ = (1 + 36 * ENNReal.ofReal CW) * Np p f (Icc 0 1) := by ring
      _ = ENNReal.ofReal (1 + 36 * CW) * Np p f (Icc 0 1) := by
          congr 1
          rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_one]
          simp
  have hfin2 : ENNReal.ofReal (1 + 36 * CW) * Np p f (Icc 0 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have h1 := ENNReal.toReal_mono hfin2 hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h1
  have h2 : (Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal ≤ (1 + 36 * CW) * B :=
    h1.trans (mul_le_mul_of_nonneg_left hNp (by positivity))
  unfold B0
  have hc : 0 ≤ 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) := by positivity
  calc 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) *
        (Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal
      ≤ 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * ((1 + 36 * CW) * B) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = (8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW)) * B := by ring

/-- Termo da série telescópica na bola: `2^{k/p} ω_p(f,2^{-k}) ≤ B · X^k`, `X = 2^{1/p-s}`. -/
lemma term_le_ball {p s : ℝ} {q : ℝ≥0∞} (hq : 0 < q) {B : ℝ} (hB : 0 ≤ B)
    {f : ℝ → ℝ} (hf : Measurable f)
    (hball : besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B) (hp : 1 ≤ p) (k : ℕ) :
    (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) ≤ B * ((2 : ℝ) ^ (1 / p - s)) ^ k := by
  obtain ⟨_, hS1, _, _, hS, _⟩ := ball_bounds hp hq hB hf hball
  have hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ ⨆ r, besovSeq (ENNReal.ofReal p) s f r :=
    fun m => le_iSup (fun r => besovSeq (ENNReal.ofReal p) s f r) m
  have hw := Wr_le_of_besov hS hbS k
  have hk : (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹ =
      ((2 : ℝ) ^ (1 / p - s)) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hX : 0 ≤ ((2 : ℝ) ^ (1 / p - s)) ^ k := by positivity
  calc (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k)
      ≤ (2 : ℝ) ^ ((k : ℝ) * (1 / p)) *
          ((⨆ r, besovSeq (ENNReal.ofReal p) s f r).toReal * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹) := by
        gcongr
    _ = (⨆ r, besovSeq (ENNReal.ofReal p) s f r).toReal *
          ((2 : ℝ) ^ ((k : ℝ) * (1 / p)) * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹) := by ring
    _ = (⨆ r, besovSeq (ENNReal.ofReal p) s f r).toReal * ((2 : ℝ) ^ (1 / p - s)) ^ k := by
        rw [hk]
    _ ≤ B * ((2 : ℝ) ^ (1 / p - s)) ^ k := mul_le_mul_of_nonneg_right hS1 hX

/-- **Cota em sup uniforme sobre bolas** (`Lema lp:lem:uniform-height (b)`). -/
theorem lam_bound_unif {p s : ℝ} (hp : 1 ≤ p) {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ B : ℝ, 1 ≤ B → ∀ f : ℝ → ℝ, Measurable f →
      besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B →
      ∀ r : ℕ, 1 ≤ r → ∀ j : ℕ, j ≤ 2 ^ r → |lam (2 ^ r) f j| ≤ C * B * LamU p s q r := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨CW, hCW, hW⟩ := FormalizacaoW.whitney_lp hp
  have hA0 : 0 ≤ 144 * CW * (2 : ℝ) ^ (1 / p) := by positivity
  have hb00 : 0 ≤ 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW) := by positivity
  -- preparação comum
  have prep : ∀ B : ℝ, 1 ≤ B → ∀ f : ℝ → ℝ, Measurable f →
      besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B →
      IntegrableOn f (Icc 0 1) ∧ Np p f (Icc 0 1) < ⊤ ∧
        B0 p CW f ≤ (8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW)) * B := by
    intro B hB f hf hball
    obtain ⟨hN1, _, _, hfin, _, _⟩ := ball_bounds hp hq (by linarith) hf hball
    refine ⟨?_, hfin, B0_le_ball hp hCW (by linarith) hf hN1 hfin⟩
    have hmem : MemLp f (ENNReal.ofReal p) (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨hf.aestronglyMeasurable, hfin⟩
    exact hmem.integrable hp1
  by_cases hlow : s < 1 / p
  · have hδ : 0 < 1 / p - s := by linarith
    have hX1 : 1 < (2 : ℝ) ^ (1 / p - s) := Real.one_lt_rpow (by norm_num) hδ
    set X : ℝ := (2 : ℝ) ^ (1 / p - s) with hXdef
    refine ⟨1 + 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW) +
      144 * CW * (2 : ℝ) ^ (1 / p) / (X - 1), ?_, ?_⟩
    · have : 0 ≤ 144 * CW * (2 : ℝ) ^ (1 / p) / (X - 1) :=
        div_nonneg hA0 (by linarith)
      linarith
    · intro B hB f hf hball r hr j hj
      obtain ⟨hfi, hfin, hB0⟩ := prep B hB f hf hball
      have hLam : LamU p s q r = X ^ r := by
        unfold LamU Lam
        rw [if_neg (not_lt.2 hlow.le), if_pos hlow, FormalizacaoL55e.two_pow_nat_mul]
      rw [hLam]
      have hnode := lam_le_B0_sum hp hW hCW hf hfi hfin r hr j hj
      have hsum : ∑ k ∈ Finset.Ico 1 r,
          144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) ≤
            144 * CW * (2 : ℝ) ^ (1 / p) * B * (X ^ r / (X - 1)) := by
        calc ∑ k ∈ Finset.Ico 1 r,
              144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k)
            = ∑ k ∈ Finset.Ico 1 r, (144 * CW * (2 : ℝ) ^ (1 / p)) *
                ((2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k)) := by
              refine Finset.sum_congr rfl (fun k _ => ?_); ring
          _ ≤ ∑ k ∈ Finset.Ico 1 r, (144 * CW * (2 : ℝ) ^ (1 / p)) * (B * X ^ k) :=
              Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
                (term_le_ball hq (by linarith) hf hball hp k) hA0)
          _ = 144 * CW * (2 : ℝ) ^ (1 / p) * B * ∑ k ∈ Finset.Ico 1 r, X ^ k := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun k _ => ?_); ring
          _ ≤ 144 * CW * (2 : ℝ) ^ (1 / p) * B * (X ^ r / (X - 1)) :=
              mul_le_mul_of_nonneg_left (geom_Ico_le hX1 r) (by positivity)
      have h1 : 1 ≤ X ^ r := one_le_pow₀ hX1.le
      have hbB : 0 ≤ B := by linarith
      have hb : (8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW)) * B ≤
          (8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW)) * B * X ^ r :=
        le_mul_of_one_le_right (by positivity) h1
      have e : 144 * CW * (2 : ℝ) ^ (1 / p) * B * (X ^ r / (X - 1)) =
          144 * CW * (2 : ℝ) ^ (1 / p) / (X - 1) * B * X ^ r := by ring
      have e2 : (1 + 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW) +
            144 * CW * (2 : ℝ) ^ (1 / p) / (X - 1)) * B * X ^ r =
          B * X ^ r + (8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW)) * B * X ^ r +
            144 * CW * (2 : ℝ) ^ (1 / p) / (X - 1) * B * X ^ r := by ring
      have hpos : 0 ≤ B * X ^ r := by positivity
      rw [e2]
      calc |lam (2 ^ r) f j| ≤ B0 p CW f + ∑ k ∈ Finset.Ico 1 r,
            144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) := hnode
        _ ≤ (8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW)) * B * X ^ r +
            144 * CW * (2 : ℝ) ^ (1 / p) / (X - 1) * B * X ^ r := by
            rw [← e] at *
            linarith
        _ ≤ _ := by linarith
  · by_cases hdiag : s = 1 / p
    · refine ⟨1 + 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW) +
        144 * CW * (2 : ℝ) ^ (1 / p), by linarith, ?_⟩
      intro B hB f hf hball r hr j hj
      obtain ⟨hfi, hfin, hB0⟩ := prep B hB f hf hball
      obtain ⟨_, _, hL1, _, _, hlq⟩ := ball_bounds hp hq (by linarith) hf hball
      have hLam : LamU p s q r = (r : ℝ) ^ thetaQ q := by
        unfold LamU Lam
        rw [if_neg (by rw [hdiag]; exact lt_irrefl _), if_neg hlow]
      rw [hLam]
      have hnode := lam_le_B0_sum hp hW hCW hf hfi hfin r hr j hj
      have hterm : ∀ k : ℕ, (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) =
          (besovSeq (ENNReal.ofReal p) s f k).toReal := by
        intro k
        unfold besovSeq Wr
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hdiag]
        have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
        rw [hcast]
      have hs1 : ∑ k ∈ Finset.Ico 1 r,
          144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) =
          144 * CW * (2 : ℝ) ^ (1 / p) *
            ∑ k ∈ Finset.Ico 1 r, (besovSeq (ENNReal.ofReal p) s f k).toReal := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← hterm k]; ring
      have hs2 : ∑ k ∈ Finset.Ico 1 r, (besovSeq (ENNReal.ofReal p) s f k).toReal ≤
          ∑ k ∈ Finset.range r, (besovSeq (ENNReal.ofReal p) s f k).toReal := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => ENNReal.toReal_nonneg)
        intro k hk
        simp only [Finset.mem_Ico] at hk
        simp only [Finset.mem_range]
        omega
      have hs3 := sum_le_lq hq hlq r
      have h1 : 1 ≤ (r : ℝ) ^ thetaQ q :=
        Real.one_le_rpow (by exact_mod_cast hr) (thetaQ_nonneg q)
      have hbB : 0 ≤ B := by linarith
      have hs4 : ∑ k ∈ Finset.Ico 1 r, (besovSeq (ENNReal.ofReal p) s f k).toReal ≤
          (r : ℝ) ^ thetaQ q * B :=
        (hs2.trans hs3).trans (mul_le_mul_of_nonneg_left hL1 (by positivity))
      have h4 : 144 * CW * (2 : ℝ) ^ (1 / p) *
          ∑ k ∈ Finset.Ico 1 r, (besovSeq (ENNReal.ofReal p) s f k).toReal ≤
          144 * CW * (2 : ℝ) ^ (1 / p) * ((r : ℝ) ^ thetaQ q * B) :=
        mul_le_mul_of_nonneg_left hs4 hA0
      have hb : (8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW)) * B ≤
          (8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW)) * B * (r : ℝ) ^ thetaQ q :=
        le_mul_of_one_le_right (by positivity) h1
      have e2 : (1 + 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW) +
            144 * CW * (2 : ℝ) ^ (1 / p)) * B * (r : ℝ) ^ thetaQ q =
          B * (r : ℝ) ^ thetaQ q +
            (8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW)) * B * (r : ℝ) ^ thetaQ q +
            144 * CW * (2 : ℝ) ^ (1 / p) * ((r : ℝ) ^ thetaQ q * B) := by ring
      have hpos : 0 ≤ B * (r : ℝ) ^ thetaQ q := by positivity
      rw [e2]
      rw [hs1] at hnode
      linarith
    · have hhigh : 1 / p < s := lt_of_le_of_ne (not_lt.1 hlow) (Ne.symm hdiag)
      have hneg : 1 / p - s < 0 := by linarith
      have hX0 : 0 ≤ (2 : ℝ) ^ (1 / p - s) := by positivity
      have hX1 : (2 : ℝ) ^ (1 / p - s) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
      set X : ℝ := (2 : ℝ) ^ (1 / p - s) with hXdef
      refine ⟨1 + 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW) +
        144 * CW * (2 : ℝ) ^ (1 / p) * (X / (1 - X)), ?_, ?_⟩
      · have : 0 ≤ 144 * CW * (2 : ℝ) ^ (1 / p) * (X / (1 - X)) :=
          mul_nonneg hA0 (div_nonneg hX0 (by linarith))
        linarith
      · intro B hB f hf hball r hr j hj
        obtain ⟨hfi, hfin, hB0⟩ := prep B hB f hf hball
        have hLam : LamU p s q r = 1 := by
          unfold LamU; rw [if_pos hhigh]
        rw [hLam, mul_one]
        have hnode := lam_le_B0_sum hp hW hCW hf hfi hfin r hr j hj
        have hgeom : ∑ k ∈ Finset.Ico 1 r, X ^ k ≤ X / (1 - X) := by
          have := geom_sum_Ico_le_of_lt_one (x := X) (m := 1) (n := r) hX0 hX1
          simpa using this
        have hbB : 0 ≤ B := by linarith
        have hsum : ∑ k ∈ Finset.Ico 1 r,
            144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) ≤
              144 * CW * (2 : ℝ) ^ (1 / p) * B * (X / (1 - X)) := by
          calc ∑ k ∈ Finset.Ico 1 r,
                144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k)
              = ∑ k ∈ Finset.Ico 1 r, (144 * CW * (2 : ℝ) ^ (1 / p)) *
                  ((2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k)) := by
                refine Finset.sum_congr rfl (fun k _ => ?_); ring
            _ ≤ ∑ k ∈ Finset.Ico 1 r, (144 * CW * (2 : ℝ) ^ (1 / p)) * (B * X ^ k) :=
                Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
                  (term_le_ball hq hbB hf hball hp k) hA0)
            _ = 144 * CW * (2 : ℝ) ^ (1 / p) * B * ∑ k ∈ Finset.Ico 1 r, X ^ k := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun k _ => ?_); ring
            _ ≤ 144 * CW * (2 : ℝ) ^ (1 / p) * B * (X / (1 - X)) :=
                mul_le_mul_of_nonneg_left hgeom (by positivity)
        have e2 : (1 + 8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW) +
              144 * CW * (2 : ℝ) ^ (1 / p) * (X / (1 - X))) * B =
            B + (8 * (1 / (2 : ℝ)) ^ (-(1 / p)) * (1 + 36 * CW)) * B +
              144 * CW * (2 : ℝ) ^ (1 / p) * B * (X / (1 - X)) := by ring
        rw [e2]
        linarith

end FormalizacaoLow
