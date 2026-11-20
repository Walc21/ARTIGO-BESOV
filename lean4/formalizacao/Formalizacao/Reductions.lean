import Formalizacao.Library
import Formalizacao.ModuloConn
import Formalizacao.LqLemmas
import Formalizacao.Schedules

/-!
# Reduções condicionais (Teoremas 1 e 2 do rascunho, a partir de `J_p`)

* `realP_le_of_approx` (Lema A): um aproximante `g ∈ Σ_N` com `‖f - g‖_p ≤ D` dá
  `R_N(f) ≤ ω_p(f, 1/N) + 5D`.
* `besov_subset_stratum` (Teorema 1, inclusão `B ⊆ R`): sob `J_p`, a agenda `H`
  com `8N^{max 1 s} ≤ H(N)` e pesos `w_k = 2^{(k+1)s}/H(2^{k+1})` em `ℓ^q`, vale
  `B^s_{p,q} ⊆ R^s_q(Σ^H)`. A outra inclusão é `stratum_subset_besov_conn`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoRed

open FormalizacaoLp FormalizacaoLq

/-- Sequência de Besov `r ↦ 2^{rs} ω_p(f, 2^{-r})`. -/
noncomputable def besovSeq (p : ℝ≥0∞) (s : ℝ) (f : ℝ → ℝ) : ℕ → ℝ≥0∞ :=
  fun r => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) * wtP p (1 / (2 : ℝ) ^ r) f

/-- Sequência do estrato `r ↦ 2^{(r+1)s} R_{2^{r+1}}(f)`. -/
noncomputable def stratSeq (p : ℝ≥0∞) (s : ℝ) (G : ℕ → Set (ℝ → ℝ)) (f : ℝ → ℝ) :
    ℕ → ℝ≥0∞ :=
  fun r => ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s)) * realP p G (2 ^ (r + 1)) f

/-- Pertencer a `B^s_{p,q}` é `‖f‖_p < ∞` e `besovSeq ∈ ℓ^q`. -/
theorem mem_besovP_iff (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) (f : ℝ → ℝ) :
    f ∈ besovP p s q ↔ eLpNorm f p vol01 < ⊤ ∧ lqNorm q (besovSeq p s f) < ⊤ := Iff.rfl

/-- Pertencer a `R^s_q(G)_p` é `‖f‖_p < ∞` e `stratSeq ∈ ℓ^q`. -/
theorem mem_stratumP_iff (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) (G : ℕ → Set (ℝ → ℝ)) (f : ℝ → ℝ) :
    f ∈ stratumP p s q G ↔ eLpNorm f p vol01 < ⊤ ∧ lqNorm q (stratSeq p s G f) < ⊤ := Iff.rfl

/-- Lema A: um aproximante `g ∈ Σ_N` com `‖f - g‖_p ≤ D` dá `R_N(f) ≤ ω_p(f,1/N) + 5D`. -/
theorem realP_le_of_approx {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : Measurable f)
    {H : ℕ → ℕ} {N : ℕ} {g : ℝ → ℝ} (hg : g ∈ Pendencias.Agenda.Sigma H N) {D : ℝ≥0∞}
    (hD : eLpNorm (f - g) p vol01 ≤ D) :
    realP p (Pendencias.Agenda.Sigma H) N f ≤ wtP p (1 / (N : ℝ)) f + 5 * D := by
  have hgm : Measurable g := measurable_sigma hg
  have h1 : realP p (Pendencias.Agenda.Sigma H) N f ≤
      eLpNorm (f - g) p vol01 + wtP p (1 / (N : ℝ)) g := by
    unfold realP
    exact iInf₂_le g hg
  have hgf : g = f + (g - f) := by abel
  have h2 : wtP p (1 / (N : ℝ)) g ≤ wtP p (1 / (N : ℝ)) f + 4 * eLpNorm (f - g) p vol01 := by
    calc wtP p (1 / (N : ℝ)) g = wtP p (1 / (N : ℝ)) (f + (g - f)) := by rw [← hgf]
      _ ≤ wtP p (1 / (N : ℝ)) f + wtP p (1 / (N : ℝ)) (g - f) :=
          wtP_add_le hp _ hf (hgm.sub hf)
      _ ≤ wtP p (1 / (N : ℝ)) f + 4 * eLpNorm (g - f) p vol01 :=
          add_le_add le_rfl (wtP_le_four hp _ (hgm.sub hf))
      _ = wtP p (1 / (N : ℝ)) f + 4 * eLpNorm (f - g) p vol01 := by
          rw [show g - f = -(f - g) from (neg_sub f g).symm, eLpNorm_neg]
  calc realP p (Pendencias.Agenda.Sigma H) N f
      ≤ eLpNorm (f - g) p vol01 + wtP p (1 / (N : ℝ)) g := h1
    _ ≤ D + (wtP p (1 / (N : ℝ)) f + 4 * D) :=
        add_le_add hD (h2.trans (add_le_add le_rfl (mul_le_mul_left' hD 4)))
    _ = wtP p (1 / (N : ℝ)) f + 5 * D := by ring

/-- `R_N(f) < ∞` para `f ∈ L^p`, pois `0 ∈ Σ_N`. -/
theorem realP_lt_top {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → ℝ} (H : ℕ → ℕ) (N : ℕ)
    (hfin : eLpNorm f p vol01 < ⊤) :
    realP p (Pendencias.Agenda.Sigma H) N f < ⊤ := by
  have h0 : (0 : ℝ → ℝ) ∈ Pendencias.Agenda.Sigma H N := Or.inl rfl
  have hw : wtP p (1 / (N : ℝ)) (0 : ℝ → ℝ) = 0 := by
    have hm : Measurable (0 : ℝ → ℝ) := measurable_zero
    have := wtP_le_four hp (1 / (N : ℝ)) hm
    rw [eLpNorm_zero, mul_zero] at this
    exact le_antisymm this (zero_le _)
  have hd : distP p f 0 = eLpNorm f p vol01 := by
    unfold distP
    simp
  have h1 : realP p (Pendencias.Agenda.Sigma H) N f ≤ distP p f 0 + wtP p (1 / (N : ℝ)) 0 := by
    unfold realP
    exact iInf₂_le (0 : ℝ → ℝ) h0
  rw [hw, hd, add_zero] at h1
  exact lt_of_le_of_lt h1 hfin

/-- Lema B: aproximante em `G_M` com índice `n ≤ M` e `‖f - g‖_p ≤ D` dá
`R^G_M(f) ≤ ω_p(f, 1/n) + 5D`, pois `ω_p` é monótono em `t`. -/
theorem realP_le_of_approx' {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : Measurable f)
    {G : ℕ → Set (ℝ → ℝ)} {M n : ℕ} (hn : 0 < n) (hnM : n ≤ M) {g : ℝ → ℝ}
    (hg : g ∈ G M) (hgm : Measurable g) {D : ℝ≥0∞}
    (hD : eLpNorm (f - g) p vol01 ≤ D) :
    realP p G M f ≤ wtP p (1 / (n : ℝ)) f + 5 * D := by
  have hmono : wtP p (1 / (M : ℝ)) g ≤ wtP p (1 / (n : ℝ)) g :=
    wtP_mono_t p g (one_div_le_one_div_of_le (by exact_mod_cast hn) (by exact_mod_cast hnM))
  have h1 : realP p G M f ≤ eLpNorm (f - g) p vol01 + wtP p (1 / (M : ℝ)) g := by
    unfold realP
    exact iInf₂_le g hg
  have hgf : g = f + (g - f) := by abel
  have h2 : wtP p (1 / (n : ℝ)) g ≤ wtP p (1 / (n : ℝ)) f + 4 * eLpNorm (f - g) p vol01 := by
    calc wtP p (1 / (n : ℝ)) g = wtP p (1 / (n : ℝ)) (f + (g - f)) := by rw [← hgf]
      _ ≤ wtP p (1 / (n : ℝ)) f + wtP p (1 / (n : ℝ)) (g - f) :=
          wtP_add_le hp _ hf (hgm.sub hf)
      _ ≤ wtP p (1 / (n : ℝ)) f + 4 * eLpNorm (g - f) p vol01 :=
          add_le_add le_rfl (wtP_le_four hp _ (hgm.sub hf))
      _ = wtP p (1 / (n : ℝ)) f + 4 * eLpNorm (f - g) p vol01 := by
          rw [show g - f = -(f - g) from (neg_sub f g).symm, eLpNorm_neg]
  calc realP p G M f ≤ eLpNorm (f - g) p vol01 + wtP p (1 / (M : ℝ)) g := h1
    _ ≤ eLpNorm (f - g) p vol01 + wtP p (1 / (n : ℝ)) g := add_le_add le_rfl hmono
    _ ≤ D + (wtP p (1 / (n : ℝ)) f + 4 * D) :=
        add_le_add hD (h2.trans (add_le_add le_rfl (mul_le_mul_left' hD 4)))
    _ = wtP p (1 / (n : ℝ)) f + 5 * D := by ring

/-- Segunda parte da Proposição `lp:prop:inverse` em `L^p`: se `0 ∈ G_N`, então
`R^G_N(f)_p ≤ ‖f‖_{L^p}`. -/
theorem realP_le_norm {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → ℝ} (G : ℕ → Set (ℝ → ℝ)) (N : ℕ)
    (h0 : (0 : ℝ → ℝ) ∈ G N) :
    realP p G N f ≤ eLpNorm f p vol01 := by
  have hw : wtP p (1 / (N : ℝ)) (0 : ℝ → ℝ) = 0 := by
    have hm : Measurable (0 : ℝ → ℝ) := measurable_zero
    have := wtP_le_four hp (1 / (N : ℝ)) hm
    rw [eLpNorm_zero, mul_zero] at this
    exact le_antisymm this (zero_le _)
  have hd : distP p f 0 = eLpNorm f p vol01 := by
    unfold distP
    simp
  have h1 : realP p G N f ≤ distP p f 0 + wtP p (1 / (N : ℝ)) 0 := by
    unfold realP
    exact iInf₂_le (0 : ℝ → ℝ) h0
  rw [hw, hd, add_zero] at h1
  exact h1

/-- `R^G_N(f) < ∞` para `f ∈ L^p`, quando `0 ∈ G_N` (família arbitrária). -/
theorem realP_lt_top_gen {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → ℝ} (G : ℕ → Set (ℝ → ℝ)) (N : ℕ)
    (h0 : (0 : ℝ → ℝ) ∈ G N) (hfin : eLpNorm f p vol01 < ⊤) :
    realP p G N f < ⊤ :=
  lt_of_le_of_lt (realP_le_norm hp G N h0) hfin

/-- Teorema 1 (inclusão `B ⊆ R`), condicional a `J_p`. -/
theorem besov_subset_stratum {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    {q : ℝ≥0∞} (hq : 0 < q) (H : ℕ → ℕ)
    (hHlow : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤ (H N : ℝ))
    (hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
      (H (2 ^ (k + 1)) : ℝ≥0∞)) < ⊤)
    {f : ℝ → ℝ} (hf : Measurable f) (hbes : f ∈ besovP p s q) :
    f ∈ stratumP p s q (Pendencias.Agenda.Sigma H) := by
  -- passa para `B^s_{p,∞}`
  have hbesTop : f ∈ besovP p s ⊤ := by
    rw [mem_besovP_iff] at hbes ⊢
    refine ⟨hbes.1, lt_of_le_of_lt ?_ hbes.2⟩
    rw [lqNorm, if_pos rfl]
    exact iSup_le_lq hq _
  obtain ⟨C0, C1, hC0, hC1, n0, hApp⟩ := hJ f hf hbesTop
  set R : ℝ := (⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|).toReal with hRdef
  -- índice a partir do qual valem os limiares
  set r1 : ℕ := max n0 ⌈4 * (R + 1)⌉₊ with hr1def
  have hk_big : ∀ k : ℕ, r1 ≤ k + 1 →
      n0 ≤ 2 ^ (k + 1) ∧ 4 * (R + 1) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
    intro k hk
    have hlt : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
    have hn0 : n0 ≤ k + 1 := le_trans (le_max_left _ _) hk
    have hc : ⌈4 * (R + 1)⌉₊ ≤ k + 1 := le_trans (le_max_right _ _) hk
    refine ⟨by omega, ?_⟩
    have h1 : 4 * (R + 1) ≤ ((k + 1 : ℕ) : ℝ) := by
      have := Nat.le_ceil (4 * (R + 1))
      have h2 : ((⌈4 * (R + 1)⌉₊ : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hc
      linarith
    have h3 : ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
    linarith
  -- constantes finitas
  have hc1 : (1 : ℝ≥0∞) + 5 * ENNReal.ofReal C0 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨by norm_num, ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩
  have hc2 : (5 : ℝ≥0∞) * ENNReal.ofReal C1 * ENNReal.ofReal (R + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  -- majoração termo a termo, para `k + 1 ≥ r1`
  have hpt : ∀ k : ℕ, r1 ≤ k + 1 →
      stratSeq p s (Pendencias.Agenda.Sigma H) f k ≤
        (1 + 5 * ENNReal.ofReal C0) * besovSeq p s f (k + 1) +
          (5 * ENNReal.ofReal C1 * ENNReal.ofReal (R + 1)) *
            (ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) / (H (2 ^ (k + 1)) : ℝ≥0∞)) := by
    intro k hk
    obtain ⟨hn0, h4⟩ := hk_big k hk
    have hNge : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    have hcast : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; rfl
    have h4' : 4 * (R + 1) ≤ (2 : ℝ) ^ (k + 1) := by rw [← hcast]; exact h4
    -- limiar de J_p para `H(2^{k+1})`
    have hthr : (H (2 ^ (k + 1)) : ℝ) ≥
        max (8 * ((2 : ℝ) ^ (k + 1)) ^ (max 1 s)) (32 * (R + 1)) := by
      have hH := hHlow (2 ^ (k + 1)) hNge
      rw [hcast] at hH
      have hb : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
      have hNs : ((2 : ℝ) ^ (k + 1)) ≤ ((2 : ℝ) ^ (k + 1)) ^ (max 1 s) := by
        calc (2 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1)) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ ((2 : ℝ) ^ (k + 1)) ^ (max 1 s) :=
              Real.rpow_le_rpow_of_exponent_le hb (le_max_left _ _)
      have h32 : 32 * (R + 1) ≤ 8 * ((2 : ℝ) ^ (k + 1)) ^ (max 1 s) := by linarith
      exact max_le (le_trans (le_refl _) hH) (le_trans h32 hH)
    obtain ⟨g, hg, hD⟩ := hApp (k + 1) hn0 (H (2 ^ (k + 1))) hthr
    have hgS : g ∈ Pendencias.Agenda.Sigma H (2 ^ (k + 1)) :=
      classNH_subset_sigma H (2 ^ (k + 1)) hg
    have hR := realP_le_of_approx hp hf hgS hD
    rw [hcast] at hR
    calc stratSeq p s (Pendencias.Agenda.Sigma H) f k
        = ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
            realP p (Pendencias.Agenda.Sigma H) (2 ^ (k + 1)) f := rfl
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
            (wtP p (1 / (2 : ℝ) ^ (k + 1)) f +
              5 * (ENNReal.ofReal C0 * wtP p (1 / (2 : ℝ) ^ (k + 1)) f +
                ENNReal.ofReal C1 * ENNReal.ofReal (R + 1) / (H (2 ^ (k + 1)) : ℝ≥0∞))) :=
          mul_le_mul_left' hR _
      _ = (1 + 5 * ENNReal.ofReal C0) * besovSeq p s f (k + 1) +
          (5 * ENNReal.ofReal C1 * ENNReal.ofReal (R + 1)) *
            (ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) / (H (2 ^ (k + 1)) : ℝ≥0∞)) := by
          simp only [besovSeq, div_eq_mul_inv]
          ring
  -- a cota `ℓ^q` da majorante
  have hlqX : lqNorm q (fun k : ℕ =>
      (1 + 5 * ENNReal.ofReal C0) * besovSeq p s f (k + 1) +
        (5 * ENNReal.ofReal C1 * ENNReal.ofReal (R + 1)) *
          (ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) / (H (2 ^ (k + 1)) : ℝ≥0∞))) < ⊤ := by
    have hsh : lqNorm q (fun k : ℕ => besovSeq p s f (k + 1)) < ⊤ :=
      lt_of_le_of_lt (lq_shift_le hq (besovSeq p s f)) ((mem_besovP_iff p s q f).1 hbes).2
    exact lq_add_lt_top hq (lq_const_mul_lt_top hq hc1 hsh) (lq_const_mul_lt_top hq hc2 hW)
  -- os termos do estrato são finitos
  have hfin : ∀ k : ℕ, stratSeq p s (Pendencias.Agenda.Sigma H) f k ≠ ⊤ := by
    intro k
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_lt (realP_lt_top hp H _ ((mem_besovP_iff p s q f).1 hbes).1))
  have hlq : lqNorm q (stratSeq p s (Pendencias.Agenda.Sigma H) f) < ⊤ :=
    lq_of_eventually_le hq (k1 := r1) hfin hlqX
      (fun k hk => hpt k (by omega))
  exact (mem_stratumP_iff p s q _ f).2 ⟨((mem_besovP_iff p s q f).1 hbes).1, hlq⟩

end FormalizacaoRed
