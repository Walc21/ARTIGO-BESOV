import Formalizacao.LpJackson1
import Formalizacao.Lemma55b
import Formalizacao.LowSup
import Formalizacao.AlturaQuant
import Formalizacao.AlturaTransfer
import Formalizacao.Whitney13

/-!
# Altura linear crítica para `s = 1/p < 1` (auditoria, Parte V)

Parte A: saltos nodais uniformes. Para `n = 2^r ≥ 2` e `f` com `ω`-controle dos níveis dyadicos,
o salto `λ_{j+1}(f) - λ_j(f)` do quase-interpolante satisfaz
`|λ_{j+1} - λ_j| ≤ 4 V₀/n + Σ_{k=1}^{r-1} K_k/n`, onde `K_k` é a inclinação máxima da diferença
de níveis `v_k = Q_{2^{k+1}}f - Q_{2^k}f` em cada célula fina (`slope_diff_le`).
A decomposição telescópica `Q_{2^r} f = Q_2 f + Σ_{k=1}^{r-1} v_k` e a estrutura afim por células
dão a cota sem nenhum fator logarítmico.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoCrit

open FormalizacaoGrid FormalizacaoQuasi FormalizacaoLp FormalizacaoLow FormalizacaoL55b
open Artigo

/-- Telescópica: `Q_{2^r} f = Q_2 f + Σ_{k=1}^{r-1} (Q_{2^{k+1}} f - Q_{2^k} f)` para `r ≥ 1`. -/
lemma Q_telescope (g : ℝ → ℝ) : ∀ r : ℕ, 1 ≤ r → ∀ x : ℝ,
    Q (2 ^ r) g x = Q 2 g x + ∑ k ∈ Finset.Ico 1 r, (Q (2 ^ (k + 1)) g x - Q (2 ^ k) g x) := by
  intro r hr x
  induction r, hr using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm]
    linarith

/-- Uma célula grossa `[c/N, (c+1)/N]` contém a fina `[j/(Ne), (j+1)/(Ne)]` para `c = j / e`. -/
lemma cell_contains {N e j : ℕ} (hN : 0 < N) (he : 0 < e) :
    (((j / e : ℕ) : ℝ) / N ≤ (j : ℝ) / ((N : ℝ) * e)) ∧
      ((j : ℝ) + 1) / ((N : ℝ) * e) ≤ (((j / e : ℕ) : ℝ) + 1) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have h1 : (j / e) * e ≤ j := Nat.div_mul_le_self j e
  have h2 : j < (j / e + 1) * e := by
    have := Nat.lt_div_mul_add (a := j) he
    nlinarith [this]
  have h1' : ((j / e : ℕ) : ℝ) * e ≤ (j : ℝ) := by exact_mod_cast h1
  have h2' : (j : ℝ) + 1 ≤ (((j / e : ℕ) : ℝ) + 1) * e := by
    have : j + 1 ≤ (j / e + 1) * e := h2
    exact_mod_cast this
  constructor
  · rw [div_le_div_iff₀ hN' (by positivity)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) hN']
    nlinarith

/-- Se `g` é afim com inclinação `≤ K` numa célula, a diferença entre dois pontos é `≤ K|b-a|`. -/
lemma abs_sub_le_of_affine {g : ℝ → ℝ} {c d K α β : ℝ} (hg : ∀ x ∈ Icc c d, g x = α + β * x)
    (hβ : |β| ≤ K) {a b : ℝ} (ha : a ∈ Icc c d) (hb : b ∈ Icc c d) :
    |g b - g a| ≤ K * |b - a| := by
  rw [hg b hb, hg a ha, show α + β * b - (α + β * a) = β * (b - a) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hβ (abs_nonneg _)

/-- Cota de inclinação de uma função afim em `[c,d]` com `|g| ≤ V` nos extremos. -/
lemma slope_le_of_endpoints {g : ℝ → ℝ} {c d V α β : ℝ} (hcd : c < d)
    (hg : ∀ x ∈ Icc c d, g x = α + β * x) (hc : |g c| ≤ V) (hd : |g d| ≤ V) :
    |β| ≤ 2 * V / (d - c) := by
  have hgd : g d - g c = β * (d - c) := by
    rw [hg d ⟨hcd.le, le_rfl⟩, hg c ⟨le_rfl, hcd.le⟩]; ring
  have h2 : |β * (d - c)| ≤ 2 * V := by
    rw [← hgd]
    calc |g d - g c| ≤ |g d| + |g c| := abs_sub _ _
      _ ≤ V + V := add_le_add hd hc
      _ = 2 * V := by ring
  rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < d - c)] at h2
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **Salto nodal uniforme.** Para `n = 2^r ≥ 2`, com inclinações `K_k` das diferenças de níveis
e sup do nível `2` limitado por `V₀` em `[0,1]`:
`|λ_{j+1}(f) - λ_j(f)| ≤ 4V₀/n + Σ_{k=1}^{r-1} K_k/n`. -/
theorem nodal_jump {f : ℝ → ℝ} {V₀ : ℝ}
    (hsup2 : ∀ x ∈ Icc (0 : ℝ) 1, |Q 2 f x| ≤ V₀)
    (K : ℕ → ℝ) (hK : ∀ k, 1 ≤ k → ∀ j, j < 2 ^ (k + 1) → ∃ α β : ℝ, |β| ≤ K k ∧
      ∀ x ∈ cell (2 ^ (k + 1)) j, Q (2 ^ (k + 1)) f x - Q (2 ^ k) f x = α + β * x)
    {r : ℕ} (hr : 1 ≤ r) {j : ℕ} (hj : j < 2 ^ r) :
    |lam (2 ^ r) f (j + 1) - lam (2 ^ r) f j| ≤
      4 * V₀ / (2 ^ r : ℕ) + ∑ k ∈ Finset.Ico 1 r, K k / (2 ^ r : ℕ) := by
  have hn1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hnpos : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 ^ r by positivity)
  have hjn : j + 1 ≤ 2 ^ r := hj
  rw [← FormalizacaoJ.Q_node hn1 f hj.le, ← FormalizacaoJ.Q_node hn1 f hjn]
  set n : ℕ := 2 ^ r with hn_def
  have hba : tn n (j + 1) - tn n j = 1 / (n : ℝ) := by
    rw [tn_succ n j hn1]; ring
  have hbaabs : |tn n (j + 1) - tn n j| = 1 / (n : ℝ) := by
    rw [hba, abs_of_nonneg (by positivity)]
  set a := tn n j with ha_def
  set b := tn n (j + 1) with hb_def
  have hab : a ≤ b := by rw [ha_def, hb_def]; exact tn_mono n (Nat.le_succ j)
  -- decomposição telescópica
  have key : Q n f b - Q n f a = (Q 2 f b - Q 2 f a) + ∑ k ∈ Finset.Ico 1 r,
      ((Q (2 ^ (k + 1)) f b - Q (2 ^ k) f b) - (Q (2 ^ (k + 1)) f a - Q (2 ^ k) f a)) := by
    have hs : ∑ k ∈ Finset.Ico 1 r, ((Q (2 ^ (k + 1)) f b - Q (2 ^ k) f b) -
        (Q (2 ^ (k + 1)) f a - Q (2 ^ k) f a)) =
        (∑ k ∈ Finset.Ico 1 r, (Q (2 ^ (k + 1)) f b - Q (2 ^ k) f b)) -
        ∑ k ∈ Finset.Ico 1 r, (Q (2 ^ (k + 1)) f a - Q (2 ^ k) f a) :=
      Finset.sum_sub_distrib _ _
    rw [hs, Q_telescope f r hr b, Q_telescope f r hr a]
    ring
  -- parte de nível 2: `Q_2 f` é afim em cada célula `[c/2,(c+1)/2]`
  have hn2 : 2 * 2 ^ (r - 1) = n := by
    rw [hn_def, ← pow_succ']; congr 1; omega
  have hcl2 : j / 2 ^ (r - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    omega
  have hpart2 : |Q 2 f b - Q 2 f a| ≤ 4 * V₀ * |b - a| := by
    obtain ⟨hc1, hc2⟩ := cell_contains (N := 2) (e := 2 ^ (r - 1)) (j := j) (by norm_num)
      (by positivity)
    have hcast : ((2 : ℕ) : ℝ) * ((2 ^ (r - 1) : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, hn2]
    rw [hcast] at hc1 hc2
    obtain ⟨α, β, hab2⟩ := FormalizacaoL55.Q_affine_on_cell (n := 2) (by norm_num) hcl2 f
    set c := j / 2 ^ (r - 1) with hc_def
    have hc1' : c ≤ 1 := by omega
    have hta : tn 2 c ≤ a := by
      rw [ha_def]; unfold tn; exact hc1
    have htb : b ≤ tn 2 (c + 1) := by
      rw [hb_def]; unfold tn; push_cast
      have hjn' : ((j : ℝ) + 1) / n ≤ ((c : ℝ) + 1) / 2 := by
        have := hc2; push_cast at this; exact this
      exact hjn'
    have haa : a ≤ tn 2 (c + 1) := by
      exact hab.trans htb
    have hbb : tn 2 c ≤ b := hta.trans hab
    have hcd : tn 2 c < tn 2 (c + 1) := by
      unfold tn; push_cast; linarith
    have hgrid : tn 2 (c + 1) - tn 2 c = 1 / 2 := by
      unfold tn; push_cast; ring
    have hsl : |β| ≤ 4 * V₀ := by
      have h0 := hsup2 (tn 2 c) ⟨by unfold tn; positivity, by unfold tn; rw [div_le_one (by norm_num)]; exact_mod_cast (show c ≤ 2 by omega)⟩
      have h1 := hsup2 (tn 2 (c + 1)) ⟨by unfold tn; positivity, by unfold tn; rw [div_le_one (by norm_num)]; exact_mod_cast (show c + 1 ≤ 2 by omega)⟩
      have := slope_le_of_endpoints (g := Q 2 f) hcd (fun x hx => hab2 x hx) h0 h1
      rw [hgrid] at this
      have e : 2 * V₀ / (1 / 2 : ℝ) = 4 * V₀ := by ring
      rw [e] at this; exact this
    have hmem_a : a ∈ Icc (tn 2 c) (tn 2 (c + 1)) := ⟨hta, haa⟩
    have hmem_b : b ∈ Icc (tn 2 c) (tn 2 (c + 1)) := ⟨hbb, htb⟩
    exact abs_sub_le_of_affine (fun x hx => hab2 x hx) hsl hmem_a hmem_b
  -- nível k: `v_k` é afim em cada célula fina `2^{k+1}` que contém `[a,b]`
  have hpartk : ∀ k ∈ Finset.Ico 1 r,
      |(Q (2 ^ (k + 1)) f b - Q (2 ^ k) f b) - (Q (2 ^ (k + 1)) f a - Q (2 ^ k) f a)| ≤
        K k / (n : ℝ) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    obtain ⟨hk1, hkr⟩ := hk
    have hNe : 2 ^ (k + 1) * 2 ^ (r - (k + 1)) = n := by
      rw [hn_def, ← pow_add]; congr 1; omega
    have hNe' : ((2 ^ (k + 1) : ℕ) : ℝ) * ((2 ^ (r - (k + 1)) : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, hNe]
    obtain ⟨hc1, hc2⟩ := cell_contains (N := 2 ^ (k + 1)) (e := 2 ^ (r - (k + 1))) (j := j)
      (by positivity) (by positivity)
    rw [hNe'] at hc1 hc2
    have hcl : j / 2 ^ (r - (k + 1)) < 2 ^ (k + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      have : j < 2 ^ (k + 1) * 2 ^ (r - (k + 1)) := by rw [hNe]; exact hj
      linarith [this, mul_comm (2 ^ (k + 1)) (2 ^ (r - (k + 1)))]
    obtain ⟨α, β, hβ, hv⟩ := hK k hk1 _ hcl
    set c := j / 2 ^ (r - (k + 1)) with hc_def
    have hta : tn (2 ^ (k + 1)) c ≤ a := by
      rw [ha_def]; unfold tn; exact hc1
    have htb : b ≤ tn (2 ^ (k + 1)) (c + 1) := by
      rw [hb_def]; unfold tn; push_cast at hc2 ⊢
      exact hc2
    have haa : a ≤ tn (2 ^ (k + 1)) (c + 1) := hab.trans htb
    have hbb : tn (2 ^ (k + 1)) c ≤ b := hta.trans hab
    have hmem_a : a ∈ cell (2 ^ (k + 1)) c := ⟨hta, haa⟩
    have hmem_b : b ∈ cell (2 ^ (k + 1)) c := ⟨hbb, htb⟩
    have := abs_sub_le_of_affine (g := fun x => Q (2 ^ (k + 1)) f x - Q (2 ^ k) f x) hv hβ
      hmem_a hmem_b
    simp only at this
    rw [hbaabs] at this
    calc _ ≤ K k * (1 / (n : ℝ)) := this
      _ = K k / (n : ℝ) := by ring
  -- combinação
  rw [key]
  calc |(Q 2 f b - Q 2 f a) + ∑ k ∈ Finset.Ico 1 r,
        ((Q (2 ^ (k + 1)) f b - Q (2 ^ k) f b) - (Q (2 ^ (k + 1)) f a - Q (2 ^ k) f a))|
      ≤ |Q 2 f b - Q 2 f a| + |∑ k ∈ Finset.Ico 1 r,
        ((Q (2 ^ (k + 1)) f b - Q (2 ^ k) f b) - (Q (2 ^ (k + 1)) f a - Q (2 ^ k) f a))| :=
        abs_add_le _ _
    _ ≤ 4 * V₀ * |b - a| + ∑ k ∈ Finset.Ico 1 r, K k / (n : ℝ) := by
        apply add_le_add hpart2
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => hpartk k hk)
    _ = 4 * V₀ / (n : ℝ) + ∑ k ∈ Finset.Ico 1 r, K k / (n : ℝ) := by
        rw [hbaabs]; ring

/-! ## Constantes dos níveis e aproximação crítica -/

/-- Soma geométrica: `Σ_{k=1}^{r-1} 2^{k+1} ≤ 2·2^r`. -/
lemma sum_pow_two_le (r : ℕ) : ∑ k ∈ Finset.Ico 1 r, (2 : ℝ) ^ (k + 1) ≤ 2 * 2 ^ r := by
  induction r with
  | zero => simp
  | succ m ih =>
    rcases Nat.lt_or_ge m 1 with h | h
    · interval_cases m; simp
    · rw [Finset.sum_Ico_succ_top h]
      have h2 : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
      linarith [ih, h2]

/-- Inclinação `K_k` da diferença de níveis, em forma explícita. -/
lemma K_eq {p CW : ℝ} (hp : 1 ≤ p) (k : ℕ) (W : ℝ) :
    8 * (1 / ((2 * 2 ^ k : ℕ) : ℝ)) ^ (-(1 / p) - 1) * (18 * CW * W) =
      144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ ((k : ℝ) * (1 / p)) * W) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have h2 : ((2 * 2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
  have e1 : ((2 : ℝ) ^ (k + 1)) ^ (1 / p + 1) = (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (1 / p) *
      (2 : ℝ) ^ ((k : ℝ) * (1 / p)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show ((k + 1 : ℕ) : ℝ) * (1 / p + 1) = ((k : ℝ) * (1 / p)) + (1 / p) + ((k + 1 : ℕ) : ℝ)
        by push_cast; ring]
    rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_natCast]
    ring
  rw [h2, one_div, Real.inv_rpow (by positivity), show -(1 / p) - 1 = -(1 / p + 1) by ring,
    Real.rpow_neg (by positivity), inv_inv, e1]
  ring

/-- Soma das inclinações: `Σ_{k=1}^{r-1} K_k / 2^r ≤ 288·CW·2^{1/p}·B` se `2^{k/p}Wr(2^k) ≤ B`. -/
lemma K_sum_le {p CW B : ℝ} (hp : 1 ≤ p) (hCW : 0 ≤ CW) (hB : 0 ≤ B) (r : ℕ)
    (W : ℕ → ℝ) (hW : ∀ k : ℕ, 1 ≤ k → (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * W (2 ^ k) ≤ B) :
    ∑ k ∈ Finset.Ico 1 r, (144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ (k + 1) *
      ((2 : ℝ) ^ ((k : ℝ) * (1 / p)) * W (2 ^ k))) / ((2 ^ r : ℕ) : ℝ) ≤
      288 * CW * (2 : ℝ) ^ (1 / p) * B := by
  have hpos : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 ^ r by positivity)
  have hc : (0 : ℝ) ≤ 144 * CW * (2 : ℝ) ^ (1 / p) := by positivity
  have hterm : ∀ k ∈ Finset.Ico 1 r, (144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ (k + 1) *
      ((2 : ℝ) ^ ((k : ℝ) * (1 / p)) * W (2 ^ k))) / ((2 ^ r : ℕ) : ℝ) ≤
      (144 * CW * (2 : ℝ) ^ (1 / p) * B) * (2 : ℝ) ^ (k + 1) / ((2 ^ r : ℕ) : ℝ) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hWk := hW k hk.1
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by positivity
    apply div_le_div_of_nonneg_right _ hpos.le
    have := mul_le_mul_of_nonneg_left hWk (mul_nonneg hc h2)
    nlinarith [this]
  calc _ ≤ ∑ k ∈ Finset.Ico 1 r, (144 * CW * (2 : ℝ) ^ (1 / p) * B) * (2 : ℝ) ^ (k + 1) /
        ((2 ^ r : ℕ) : ℝ) := Finset.sum_le_sum hterm
    _ = (144 * CW * (2 : ℝ) ^ (1 / p) * B) * (∑ k ∈ Finset.Ico 1 r, (2 : ℝ) ^ (k + 1)) /
        ((2 ^ r : ℕ) : ℝ) := by
        rw [← Finset.sum_div, Finset.mul_sum]
    _ ≤ (144 * CW * (2 : ℝ) ^ (1 / p) * B) * (2 * 2 ^ r) / ((2 ^ r : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hpos.le
        apply mul_le_mul_of_nonneg_left (sum_pow_two_le r)
        positivity
    _ = 288 * CW * (2 : ℝ) ^ (1 / p) * B := by
        have hcast : ((2 ^ r : ℕ) : ℝ) = 2 ^ r := by push_cast; ring
        rw [hcast]
        have : (2 : ℝ) ^ r ≠ 0 := by positivity
        field_simp
        ring

/-- **Aproximação crítica.** Para `f` com controle `2^{k/p} Wr(2^k) ≤ B` (e `p > 1`), existe
`T ∈ A_{2^r,H}` com `|Q_{2^r} f - T| ≤ 8(M+1)/H` em `[0,1]`, onde
`M = B₀ + 144·CW·2^{1/p}·B·r` e `H` satisfaz `8·2^r ≤ H`, `16(M+1) ≤ H` e `2^r(J+1) ≤ H`
com `J = 4B₀ + 288·CW·2^{1/p}·B`. -/
theorem critical_approx {p CW : ℝ} (hp : 1 < p) (hW : FormalizacaoCor.WhitneyLp p CW)
    (hCW : 0 ≤ CW) {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {B : ℝ} (hB : 0 ≤ B)
    (hWB : ∀ k : ℕ, 1 ≤ k → (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) ≤ B)
    {r : ℕ} (hr : 1 ≤ r) {H : ℕ}
    (hH1 : 8 * (2 : ℝ) ^ r ≤ H)
    (hH2 : 16 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * r + 1) ≤ H)
    (hH3 : (2 : ℝ) ^ r * (4 * B0 p CW f + 288 * CW * (2 : ℝ) ^ (1 / p) * B + 1) ≤ H) :
    ∃ T : LTree, AdmNH (2 ^ r) H T ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |Q (2 ^ r) f x - T.eval 0 0 x| ≤
        8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * r + 1) / H := by
  have hp1 : 1 ≤ p := hp.le
  set V0 := B0 p CW f with hV0def
  have hV0nn : 0 ≤ V0 := FormalizacaoLow.B0_nonneg p CW f
  have hsup2 : ∀ x ∈ Icc (0 : ℝ) 1, |Q 2 f x| ≤ V0 := by
    intro x hx
    have := Q_sup_le hp1 hW hCW hf hfi hfin hx 1 le_rfl
    simpa using this
  set Mr : ℝ := V0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * r with hMr
  have hM0 : 0 ≤ Mr := by positivity
  have hsupr : ∀ x ∈ Icc (0 : ℝ) 1, |Q (2 ^ r) f x| ≤ Mr := by
    intro x hx
    have h1 := Q_sup_le hp1 hW hCW hf hfi hfin hx r hr
    refine h1.trans ?_
    have hsum : ∑ k ∈ Finset.Ico 1 r, 144 * CW * (2 : ℝ) ^ (1 / p) *
        (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) ≤
        ∑ k ∈ Finset.Ico 1 r, 144 * CW * (2 : ℝ) ^ (1 / p) * B := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_Ico] at hk
      have := mul_le_mul_of_nonneg_left (hWB k hk.1) (by positivity : (0 : ℝ) ≤ 144 * CW * (2 : ℝ) ^ (1 / p))
      linarith [this, show 144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) =
        144 * CW * (2 : ℝ) ^ (1 / p) * ((2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k)) by ring]
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
    have hcard : ((r - 1 : ℕ) : ℝ) ≤ r := by
      have : r - 1 ≤ r := Nat.sub_le r 1
      exact_mod_cast this
    have hK0 : 0 ≤ 144 * CW * (2 : ℝ) ^ (1 / p) * B := by positivity
    have hfin2 : ((r - 1 : ℕ) : ℝ) * (144 * CW * (2 : ℝ) ^ (1 / p) * B) ≤
        (r : ℝ) * (144 * CW * (2 : ℝ) ^ (1 / p) * B) := mul_le_mul_of_nonneg_right hcard hK0
    have h2 : V0 + ∑ k ∈ Finset.Ico 1 r, 144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) *
        Wr p f (2 ^ k) ≤ V0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * r := by
      linarith [hsum, hfin2]
    exact h2
  -- inclinações dos níveis
  set K : ℕ → ℝ := fun k => 144 * CW * (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ (k + 1) *
    ((2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k)) with hKdef
  have hK : ∀ k, 1 ≤ k → ∀ j, j < 2 ^ (k + 1) → ∃ α β : ℝ, |β| ≤ K k ∧
      ∀ x ∈ cell (2 ^ (k + 1)) j, Q (2 ^ (k + 1)) f x - Q (2 ^ k) f x = α + β * x := by
    intro k hk j hj
    have hn2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hj' : j < 2 * 2 ^ k := by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    obtain ⟨β, hβ, α, hα⟩ := slope_diff_le hp1 hW hCW hn2 hf hfi hfin hj'
    have e : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
    rw [K_eq (CW := CW) hp1 k (Wr p f (2 ^ k))] at hβ
    rw [e] at hα
    refine ⟨α, β, ?_, hα⟩
    rw [hKdef]
    exact hβ
  -- salto nodal
  have hjump : ∀ j, j < 2 ^ r → |lam (2 ^ r) f (j + 1) - lam (2 ^ r) f j| ≤
      4 * V0 + 288 * CW * (2 : ℝ) ^ (1 / p) * B := by
    intro j hj
    have h1 := nodal_jump (f := f) (V₀ := V0) hsup2 K hK hr hj
    have hKs := K_sum_le (p := p) (CW := CW) (B := B) hp1 hCW hB r (Wr p f) hWB
    have hn1 : (1 : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    have hV : 4 * V0 / ((2 ^ r : ℕ) : ℝ) ≤ 4 * V0 := by
      apply div_le_of_le_mul₀ (by positivity) (by positivity)
      nlinarith
    refine h1.trans ?_
    have hKs' : ∑ k ∈ Finset.Ico 1 r, K k / ((2 ^ r : ℕ) : ℝ) ≤ 288 * CW * (2 : ℝ) ^ (1 / p) * B := by
      simpa [hKdef] using hKs
    linarith [hV, hKs']
  -- aproximação: quantização com salto (Lema de quantização com salto `J`)
  have hn1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hsupn : ∀ j : ℕ, j ≤ 2 ^ r → |lam (2 ^ r) f j| ≤ Mr := by
    intro j hj
    rw [← FormalizacaoJ.Q_node hn1 f hj]
    apply hsupr
    refine ⟨?_, ?_⟩
    · unfold tn; positivity
    · unfold tn
      rw [div_le_one (by positivity)]
      exact_mod_cast hj
  set y : ℤ → ℝ := fun m => lam (2 ^ r) f m.toNat with hy_def
  have hy : ∀ m : ℤ, 0 ≤ m → m ≤ ((2 ^ r : ℕ) : ℤ) → |y m| ≤ Mr := by
    intro m hm hmn
    have hj : m.toNat ≤ 2 ^ r := by omega
    exact hsupn _ hj
  have hJy : ∀ m : ℤ, 0 ≤ m → m < ((2 ^ r : ℕ) : ℤ) →
      |y (m + 1) - y m| ≤ 4 * V0 + 288 * CW * (2 : ℝ) ^ (1 / p) * B := by
    intro m hm hmn
    have hsucc : (m + 1).toNat = m.toNat + 1 := by omega
    have hj : m.toNat < 2 ^ r := by omega
    simp only [hy_def]
    rw [hsucc]
    exact hjump m.toNat hj
  have hM' : 0 ≤ Mr := hM0
  obtain ⟨T, hT, hg⟩ := FormalizacaoAltura.quantization_jump (r := r) (M := Mr)
    (J := 4 * V0 + 288 * CW * (2 : ℝ) ^ (1 / p) * B) (y := y) hM' hy hJy hH1 hH2 hH3
  refine ⟨T, hT, fun x hx => ?_⟩
  have hcond1 : ∀ m : ℤ, 0 ≤ m → m ≤ ((2 ^ r : ℕ) : ℤ) → Q (2 ^ r) f ((m : ℝ) / 2 ^ r) = y m := by
    intro m hm hmn
    have hj : m.toNat ≤ 2 ^ r := by omega
    rw [hy_def]
    simp only
    rw [← FormalizacaoJ.Q_node hn1 f hj]
    congr 1
    unfold tn
    have hcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm
    rw [hcast]
    push_cast
    ring
  have hcond2 : ∀ m : ℤ, 0 ≤ m → m < ((2 ^ r : ℕ) : ℤ) →
      ∃ α β : ℝ, ∀ x ∈ cellIcc r m, Q (2 ^ r) f x = α + β * x := by
    intro m hm hmn
    have hj : m.toNat < 2 ^ r := by omega
    obtain ⟨α, β, hab⟩ := FormalizacaoL55.Q_affine_on_cell hn1 hj f
    refine ⟨α, β, fun x hx => hab x ?_⟩
    have hcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm
    unfold cellIcc at hx
    unfold cell tn
    push_cast
    rw [hcast]
    exact hx
  have hgx := hg (Q (2 ^ r) f) hcond1 hcond2 x (by
    unfold cellIcc
    have : x ∈ Icc (0 : ℝ) 1 := hx
    simpa using this)
  simpa using hgx

end FormalizacaoCrit
