import Formalizacao.Whitney13
import Formalizacao.LpJackson1
import Formalizacao.Reductions
import Formalizacao.LowSum

/-!
# Regimes `s ≤ 1/p`, parte 4: cota em sup dos valores nodais

`Lema lp:lem:sup-bound` do artigo, na forma «existe `K ≥ 1` (dependendo de `f`)»:
para `f ∈ B^s_{p,q}` mensurável, `s ≤ 1/p`, vale `|λ_j(f)| ≤ K Λ_r` (`0 ≤ j ≤ 2^r`, `r ≥ 1`), com
`Λ_r = 2^{r(1/p - s)}` se `s < 1/p` e `Λ_r = r^{θ_q}` se `s = 1/p`.

A prova usa a série telescópica `Q_{2^r} f = Q_2 f + ∑_{k=1}^{r-1} v_k`, a cota
`‖v_k‖_∞ ≤ 144 C_W 2^{1/p} 2^{k/p} ω_p(f, 2^{-k})` já formalizada (`sup_diff_le`) e, em `s = 1/p`,
as somas parciais de `ℓ^q` (`FormalizacaoLow.sum_le_lq`).
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid FormalizacaoLp FormalizacaoL55 FormalizacaoL55b
  FormalizacaoL55c FormalizacaoRed

namespace FormalizacaoLow

/-- Constante da primeira escala (`Q_2 f`), como em `F0_bound`. -/
noncomputable def B0 (p CW : ℝ) (f : ℝ → ℝ) : ℝ :=
  8 * (1 / (2 : ℝ)) ^ (-(1 / p)) *
    (Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal

lemma B0_nonneg (p CW : ℝ) (f : ℝ → ℝ) : 0 ≤ B0 p CW f := by
  unfold B0; positivity

/-- Passo da série telescópica, para `k ≥ 1`, em `[0,1]`. -/
lemma step_le {p CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |Q (2 ^ (k + 1)) f x - Q (2 ^ k) f x| ≤
      144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) := by
  have hn2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2k : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
  have hbase := sup_diff_le hp hW hCW hn2 hf hfi hfin hx
  rw [h2k] at hbase
  have hA : ((1 : ℝ) / ((2 : ℝ) ^ (k + 1))) ^ (-(1 / p)) =
      (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p)) := by
    rw [two_pow_neg_rpow]
  have hcast : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
  rw [hcast, hA] at hbase
  have e1 : (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p)) =
      (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [e1] at hbase
  calc |Q (2 ^ (k + 1)) f x - Q (2 ^ k) f x|
      ≤ 8 * ((2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p))) * (18 * CW * Wr p f (2 ^ k)) :=
        hbase
    _ = _ := by ring

/-- Série telescópica: `|Q_{2^r} f| ≤ B_0 + ∑_{k=1}^{r-1} (passo k)`, em `[0,1]`. -/
theorem Q_sup_le {p CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∀ r : ℕ, 1 ≤ r → |Q (2 ^ r) f x| ≤ B0 p CW f +
      ∑ k ∈ Finset.Ico 1 r,
        144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    have h0 := F0_bound hp hW hCW hf hfi hfin hx
    have e : Q (2 ^ 1) f x = F f 0 x := by simp [F]
    rw [e]
    simpa [B0] using h0
  | succ r hr ih =>
    have hs := step_le hp hW hCW hf hfi hfin hr hx
    rw [Finset.sum_Ico_succ_top hr]
    calc |Q (2 ^ (r + 1)) f x|
        = |Q (2 ^ r) f x + (Q (2 ^ (r + 1)) f x - Q (2 ^ r) f x)| := by ring_nf
      _ ≤ |Q (2 ^ r) f x| + |Q (2 ^ (r + 1)) f x - Q (2 ^ r) f x| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- Os nós `j/n` estão em `[0,1]` para `j ≤ n`. -/
lemma tn_mem_Icc {n : ℕ} (hn : 1 ≤ n) {j : ℕ} (hj : j ≤ n) : tn n j ∈ Icc (0 : ℝ) 1 := by
  refine ⟨FormalizacaoW.tn_zero_le n j, ?_⟩
  have := tn_mono n hj
  rwa [FormalizacaoW.tn_n hn] at this

/-- Fator de crescimento `Λ_r`. -/
noncomputable def Lam (p s : ℝ) (q : ℝ≥0∞) (r : ℕ) : ℝ :=
  if s < 1 / p then (2 : ℝ) ^ ((r : ℝ) * (1 / p - s)) else (r : ℝ) ^ thetaQ q

lemma one_le_Lam (p s : ℝ) (q : ℝ≥0∞) {r : ℕ} (hr : 1 ≤ r) (hs : s ≤ 1 / p) :
    1 ≤ Lam p s q r := by
  unfold Lam
  split_ifs with h
  · exact Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg r) (by linarith))
  · exact Real.one_le_rpow (by exact_mod_cast hr) (thetaQ_nonneg q)

/-- Cota geométrica: para `X > 1`, `∑_{k ∈ [1,r)} X^k ≤ X^r/(X-1)`. -/
lemma geom_Ico_le {X : ℝ} (hX : 1 < X) (r : ℕ) :
    ∑ k ∈ Finset.Ico 1 r, X ^ k ≤ X ^ r / (X - 1) := by
  have h1 : ∑ k ∈ Finset.Ico 1 r, X ^ k ≤ ∑ k ∈ Finset.range r, X ^ k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
    intro k hk
    simp only [Finset.mem_Ico] at hk
    simp only [Finset.mem_range]
    omega
  rw [geom_sum_eq hX.ne' r] at h1
  refine h1.trans ?_
  have hpos : 0 < X - 1 := by linarith
  exact div_le_div_of_nonneg_right (by linarith) hpos.le

/-- **Cota em sup dos valores nodais** (`Lema lp:lem:sup-bound`). -/
theorem lam_bound {p s : ℝ} (hp : 1 ≤ p) (hs : s ≤ 1 / p) {q : ℝ≥0∞} (hq : 0 < q)
    {f : ℝ → ℝ} (hf : Measurable f) (hbes : f ∈ besovP (ENNReal.ofReal p) s q) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ r : ℕ, 1 ≤ r → ∀ j : ℕ, j ≤ 2 ^ r →
      |lam (2 ^ r) f j| ≤ K * Lam p s q r := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hbes' := (mem_besovP_iff _ _ _ _).1 hbes
  obtain ⟨hfin', hlq⟩ := hbes'
  have hfin : Np p f (Icc 0 1) < ⊤ := hfin'
  have hfi : IntegrableOn f (Icc 0 1) := by
    have hmem : MemLp f (ENNReal.ofReal p) (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨hf.aestronglyMeasurable, hfin'⟩
    exact hmem.integrable hp1
  obtain ⟨CW, hCW, hW⟩ := FormalizacaoW.whitney_lp hp
  have hB0 := B0_nonneg p CW f
  have hA0 : 0 ≤ 144 * CW * (2 : ℝ) ^ (1 / p) := by positivity
  have hnode : ∀ r : ℕ, 1 ≤ r → ∀ j : ℕ, j ≤ 2 ^ r →
      |lam (2 ^ r) f j| ≤ B0 p CW f + ∑ k ∈ Finset.Ico 1 r,
        144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) := by
    intro r hr j hj
    have hn : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    rw [← FormalizacaoJ.Q_node hn f hj]
    exact Q_sup_le hp hW hCW hf hfi hfin (tn_mem_Icc hn hj) r hr
  by_cases hlow : s < 1 / p
  · have hδ : 0 < 1 / p - s := by linarith
    set X : ℝ := (2 : ℝ) ^ (1 / p - s) with hX
    have hX1 : 1 < X := Real.one_lt_rpow (by norm_num) hδ
    set S : ℝ≥0∞ := ⨆ r, besovSeq (ENNReal.ofReal p) s f r with hSdef
    have hS : S < ⊤ := lt_of_le_of_lt (FormalizacaoLq.iSup_le_lq hq _) hlq
    have hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
        wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S := fun m =>
      le_iSup (fun r => besovSeq (ENNReal.ofReal p) s f r) m
    have hS0 : 0 ≤ S.toReal := ENNReal.toReal_nonneg
    have hterm : ∀ k : ℕ, (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) ≤ S.toReal * X ^ k := by
      intro k
      have hw := Wr_le_of_besov hS hbS k
      have hk : (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹ = X ^ k := by
        rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        ring
      calc (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k)
          ≤ (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * (S.toReal * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹) := by
            gcongr
        _ = S.toReal * ((2 : ℝ) ^ ((k : ℝ) * (1 / p)) * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹) := by ring
        _ = S.toReal * X ^ k := by rw [hk]
    have hsum : ∀ r : ℕ, ∑ k ∈ Finset.Ico 1 r,
        144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) ≤
          144 * CW * (2 : ℝ) ^ (1 / p) * S.toReal * (X ^ r / (X - 1)) := by
      intro r
      calc ∑ k ∈ Finset.Ico 1 r,
            144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k)
          = ∑ k ∈ Finset.Ico 1 r, (144 * CW * (2 : ℝ) ^ (1 / p)) *
              ((2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k)) := by
            refine Finset.sum_congr rfl (fun k _ => ?_); ring
        _ ≤ ∑ k ∈ Finset.Ico 1 r, (144 * CW * (2 : ℝ) ^ (1 / p)) * (S.toReal * X ^ k) :=
            Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hterm k) hA0)
        _ = 144 * CW * (2 : ℝ) ^ (1 / p) * S.toReal * ∑ k ∈ Finset.Ico 1 r, X ^ k := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => ?_); ring
        _ ≤ 144 * CW * (2 : ℝ) ^ (1 / p) * S.toReal * (X ^ r / (X - 1)) :=
            mul_le_mul_of_nonneg_left (geom_Ico_le hX1 r) (by positivity)
    refine ⟨1 + B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * S.toReal / (X - 1), ?_, ?_⟩
    · have : 0 ≤ 144 * CW * (2 : ℝ) ^ (1 / p) * S.toReal / (X - 1) :=
        div_nonneg (by positivity) (by linarith)
      linarith
    · intro r hr j hj
      have hLam : Lam p s q r = X ^ r := by
        unfold Lam
        rw [if_pos hlow, FormalizacaoL55e.two_pow_nat_mul]
      rw [hLam]
      have h1 : 1 ≤ X ^ r := one_le_pow₀ hX1.le
      have hb : B0 p CW f ≤ B0 p CW f * X ^ r := le_mul_of_one_le_right hB0 h1
      have e : 144 * CW * (2 : ℝ) ^ (1 / p) * S.toReal * (X ^ r / (X - 1)) =
          144 * CW * (2 : ℝ) ^ (1 / p) * S.toReal / (X - 1) * X ^ r := by ring
      have e2 : (1 + B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * S.toReal / (X - 1)) * X ^ r =
          X ^ r + B0 p CW f * X ^ r +
            144 * CW * (2 : ℝ) ^ (1 / p) * S.toReal / (X - 1) * X ^ r := by ring
      have h3 := (hnode r hr j hj).trans (add_le_add_right (hsum r) _)
      rw [e2]
      rw [e] at h3
      linarith
  · have hseq : s = 1 / p := le_antisymm hs (not_lt.1 hlow)
    set L : ℝ := (lqNorm q (besovSeq (ENNReal.ofReal p) s f)).toReal with hL
    have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
    have hterm : ∀ k : ℕ, (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) =
        (besovSeq (ENNReal.ofReal p) s f k).toReal := by
      intro k
      unfold besovSeq Wr
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hseq]
      have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
      rw [hcast]
    refine ⟨1 + B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * L, ?_, ?_⟩
    · have : 0 ≤ 144 * CW * (2 : ℝ) ^ (1 / p) * L := by positivity
      linarith
    · intro r hr j hj
      have hLam : Lam p s q r = (r : ℝ) ^ thetaQ q := by
        unfold Lam
        rw [if_neg hlow]
      rw [hLam]
      have h1 : 1 ≤ (r : ℝ) ^ thetaQ q :=
        Real.one_le_rpow (by exact_mod_cast hr) (thetaQ_nonneg q)
      have hb : B0 p CW f ≤ B0 p CW f * (r : ℝ) ^ thetaQ q := le_mul_of_one_le_right hB0 h1
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
      have h3 := hnode r hr j hj
      rw [hs1] at h3
      have h4 : 144 * CW * (2 : ℝ) ^ (1 / p) *
          ∑ k ∈ Finset.Ico 1 r, (besovSeq (ENNReal.ofReal p) s f k).toReal ≤
          144 * CW * (2 : ℝ) ^ (1 / p) * ((r : ℝ) ^ thetaQ q * L) :=
        mul_le_mul_of_nonneg_left (hs2.trans hs3) hA0
      have e2 : (1 + B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * L) * (r : ℝ) ^ thetaQ q =
          (r : ℝ) ^ thetaQ q + B0 p CW f * (r : ℝ) ^ thetaQ q +
            144 * CW * (2 : ℝ) ^ (1 / p) * ((r : ℝ) ^ thetaQ q * L) := by ring
      rw [e2]
      linarith

end FormalizacaoLow
