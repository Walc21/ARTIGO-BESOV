import Mathlib

/-!
# Arcabouço abstrato do módulo em `ENNReal` (versão para `L^p`)

Versão de `Formalizacao.Modulo` com valores em `ℝ≥0∞`, sobre um grupo aditivo `X`
com uma norma `nrm : X → ℝ≥0∞` (que pode ser a norma `L^p`). Os axiomas são os
do rascunho (subaditividade, cota `ω g t ≤ 4 nrm g`, monotonia em `t`).

Definem-se o funcional de realização, o estrato e o espaço de Besov abstratos, e
prova-se a desigualdade inversa. A conexão com `L^p` está em `Formalizacao.ModuloConn`.
-/

open scoped ENNReal

namespace Formalizacao.ModE

variable {X : Type*} [AddCommGroup X]

/-- Dados do módulo sobre `X`, com norma `nrm`. -/
structure ModuloE (nrm : X → ℝ≥0∞) where
  /-- O módulo `ω(f, t)`. -/
  ω : X → ℝ → ℝ≥0∞
  /-- Subaditividade. -/
  subadd : ∀ f g : X, ∀ t : ℝ, ω (f + g) t ≤ ω f t + ω g t
  /-- Cota pela norma: `ω g t ≤ 4 nrm g`. -/
  bound : ∀ g : X, ∀ t : ℝ, ω g t ≤ 4 * nrm g
  /-- Monotonia em `t`. -/
  mono : ∀ f : X, ∀ {s t : ℝ}, s ≤ t → ω f s ≤ ω f t

variable {nrm : X → ℝ≥0∞}

/-- Norma `ℓ^q` de uma sequência em `ℝ≥0∞` (`q = ∞` é o supremo). -/
noncomputable def lqE (q : ℝ≥0∞) (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  if q = ⊤ then ⨆ r, a r else (∑' r, a r ^ q.toReal) ^ (q.toReal⁻¹)

/-- Funcional de realização abstrato `R_N^G(f) = inf_{g ∈ G_N} (nrm(f - g) + ω(g, 1/N))`. -/
noncomputable def realE (M : ModuloE nrm) (G : ℕ → Set X) (N : ℕ) (f : X) : ℝ≥0∞ :=
  ⨅ g ∈ G N, nrm (f - g) + M.ω g (1 / (N : ℝ))

/-- Estrato abstrato `R^s_q(G) = {f : (2^{(r+1)s} R_{2^{r+1}}(f))_{r} ∈ ℓ^q}`. -/
noncomputable def stratumE (M : ModuloE nrm) (G : ℕ → Set X) (s : ℝ) (q : ℝ≥0∞) : Set X :=
  {f | nrm f < ⊤ ∧ lqE q (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s)) *
      realE M G (2 ^ (r + 1)) f) < ⊤}

/-- Espaço de Besov abstrato `B^s_q = {f : nrm f < ∞, (2^{rs} ω(f, 2^{-r}))_r ∈ ℓ^q}`. -/
noncomputable def besovE (M : ModuloE nrm) (s : ℝ) (q : ℝ≥0∞) : Set X :=
  {f | nrm f < ⊤ ∧ lqE q (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) *
      M.ω f (1 / (2 : ℝ) ^ r)) < ⊤}

/-- Desigualdade inversa abstrata: `ω(f, 1/N) ≤ 4 R_N^G(f)`, para qualquer família `G`. -/
theorem inverse_E (M : ModuloE nrm) (G : ℕ → Set X) (N : ℕ) (f : X) :
    M.ω f (1 / (N : ℝ)) ≤ 4 * realE M G N f := by
  have key : ∀ g ∈ G N, M.ω f (1 / (N : ℝ)) ≤ 4 * (nrm (f - g) + M.ω g (1 / (N : ℝ))) := by
    intro g _
    calc M.ω f (1 / (N : ℝ)) = M.ω ((f - g) + g) (1 / (N : ℝ)) := by
          rw [sub_add_cancel]
      _ ≤ M.ω (f - g) (1 / (N : ℝ)) + M.ω g (1 / (N : ℝ)) := M.subadd _ _ _
      _ ≤ 4 * nrm (f - g) + M.ω g (1 / (N : ℝ)) := add_le_add (M.bound _ _) le_rfl
      _ ≤ 4 * (nrm (f - g) + M.ω g (1 / (N : ℝ))) := by
          rw [mul_add]
          exact add_le_add le_rfl (le_mul_of_one_le_left (zero_le _) (by norm_num))
  have h4z : (4 : ℝ≥0∞) ≠ 0 := by norm_num
  have h4t : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  unfold realE
  simp only [ENNReal.mul_iInf_of_ne h4z h4t]
  exact le_iInf₂ fun g hg => key g hg

/-- Domínio em `ℓ^q` (`0 < q`): se `a 0 < ∞`, `a (n+1) ≤ c b_n` e `b ∈ ℓ^q`, então `a ∈ ℓ^q`. -/
theorem lqE_lt_top_of_succ_le {q : ℝ≥0∞} (hq : 0 < q) {a b : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (ha0 : a 0 ≠ ⊤) (hab : ∀ n, a (n + 1) ≤ c * b n)
    (hb : lqE q b < ⊤) : lqE q a < ⊤ := by
  unfold lqE at hb ⊢
  split_ifs at hb ⊢ with hqt
  · -- caso `q = ∞`: supremo
    have hcB : c * (⨆ r, b r) ≠ ⊤ := ENNReal.mul_ne_top hc hb.ne
    have hbound : ∀ r, a r ≤ a 0 + c * ⨆ r, b r := by
      intro r
      cases r with
      | zero => exact le_self_add
      | succ n =>
        calc a (n + 1) ≤ c * b n := hab n
          _ ≤ c * ⨆ r, b r := mul_le_mul_left' (le_iSup b n) c
          _ ≤ a 0 + c * ⨆ r, b r := le_add_self
    exact lt_of_le_of_lt (iSup_le hbound) (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 ha0,
      lt_top_iff_ne_top.2 hcB⟩)
  · -- caso `0 < q < ∞`
    have hp0 : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
    have hbsum : ∑' r, b r ^ q.toReal < ⊤ :=
      (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hp0)).1 hb
    have hsplit : ∑' r, a r ^ q.toReal = a 0 ^ q.toReal + ∑' n, a (n + 1) ^ q.toReal :=
      tsum_eq_zero_add' (ENNReal.summable (f := fun n : ℕ => a (n + 1) ^ q.toReal))
    have htail : ∑' n, a (n + 1) ^ q.toReal ≤ ∑' n, c ^ q.toReal * b n ^ q.toReal := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      exact ENNReal.rpow_le_rpow (hab n) hp0.le
    have hmul : ∑' n, c ^ q.toReal * b n ^ q.toReal = c ^ q.toReal * ∑' n, b n ^ q.toReal :=
      ENNReal.tsum_mul_left
    have hfin : c ^ q.toReal * ∑' n, b n ^ q.toReal < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp0.le hc) hbsum
    have hasum : ∑' r, a r ^ q.toReal < ⊤ := by
      rw [hsplit]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.rpow_lt_top_of_nonneg hp0.le ha0,
        lt_of_le_of_lt (htail.trans hmul.le) hfin⟩
    exact (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hp0)).2 hasum

/-- Corolário de inclusão abstrato `R^s_q(G) ⊆ B^s_q` (para `0 < q`), em `ENNReal`. -/
theorem stratum_subset_besovE (M : ModuloE nrm) (G : ℕ → Set X) (s : ℝ) (q : ℝ≥0∞)
    (hq : 0 < q) : stratumE M G s q ⊆ besovE M s q := by
  rintro f ⟨hfn, hf⟩
  refine ⟨hfn, ?_⟩
  apply lqE_lt_top_of_succ_le (c := 4)
    (b := fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s)) *
      realE M G (2 ^ (r + 1)) f) hq (by norm_num) ?_ ?_ hf
  · have h1 := M.bound f 1
    have h2 : (4 : ℝ≥0∞) * nrm f ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hfn.ne
    simp only [pow_zero, div_one, Nat.cast_zero, zero_mul, Real.rpow_zero,
      ENNReal.ofReal_one, one_mul]
    exact ne_top_of_le_ne_top h2 h1
  · intro n
    have hI := inverse_E M G (2 ^ (n + 1)) f
    push_cast at hI
    calc ENNReal.ofReal ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * s)) * M.ω f (1 / (2 : ℝ) ^ (n + 1))
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * s)) * (4 * realE M G (2 ^ (n + 1)) f) :=
          mul_le_mul_left' hI _
      _ = 4 * (ENNReal.ofReal ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * s)) *
          realE M G (2 ^ (n + 1)) f) := by ring

end Formalizacao.ModE
