import Formalizacao.Reductions
import Formalizacao.Schedules
import Formalizacao.ModuloConn

/-!
# Reduções condicionais: Conjectura 2 (estabilidade por inclusão de redes), a partir de `J_p`

Dada uma família aninhada `𝒩` que contém a biblioteca `Σ^H` com constante `c ≥ 1`
(`Σ^H_N ⊆ 𝒩_{⌈cN⌉}`), mostra-se que, sob `J_p` e as mesmas hipóteses de pesos do Teorema 1,
`B^s_{p,q} ⊆ R^s_q(𝒩)` para funções mensuráveis. A inclusão reversa é
`stratum_subset_besov_conn`, sob a hipótese de que os elementos de `𝒩` são mensuráveis.

Escolhe-se `e` com `c ≤ 2^e`. Para `M = 2^{k+1}` e `n = 2^{k+1-e}` tem-se `⌈cn⌉ ≤ M`,
de modo que o aproximante de `Σ^H_n` pertence a `𝒩_M`. A soma em `ℓ^q` é então dominada
por uma cauda deslocada de `a` e de `w`, via `lq_tail_le`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace FormalizacaoStab

open FormalizacaoLp FormalizacaoLq FormalizacaoRed FormalizacaoSched

/-- Famílias aninhadas são monótonas: `N ≤ M ⇒ 𝒩_N ⊆ 𝒩_M`. -/
theorem fam_mono (𝒩 : ℕ → Set (ℝ → ℝ)) (hnest : ∀ N, 𝒩 N ⊆ 𝒩 (N + 1)) {a b : ℕ}
    (hab : a ≤ b) : 𝒩 a ⊆ 𝒩 b := by
  induction b, hab using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact ih.trans (hnest n)

/-- **Teorema 2 (inclusão `B ⊆ R^𝒩`)**, condicional a `J_p`, para `f` mensurável. -/
theorem besov_subset_stratum_fam {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    {q : ℝ≥0∞} (hq : 0 < q) (H : ℕ → ℕ)
    (hHlow : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤ (H N : ℝ))
    (hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
      (H (2 ^ (k + 1)) : ℝ≥0∞)) < ⊤)
    (𝒩 : ℕ → Set (ℝ → ℝ)) (h0 : ∀ N, (0 : ℝ → ℝ) ∈ 𝒩 N)
    (hnest : ∀ N, 𝒩 N ⊆ 𝒩 (N + 1))
    {c : ℝ} (hc : 1 ≤ c) (hcont : ∀ N, Pendencias.Agenda.Sigma H N ⊆ 𝒩 ⌈c * N⌉₊)
    {f : ℝ → ℝ} (hf : Measurable f) (hbes : f ∈ besovP p s q) :
    f ∈ stratumP p s q 𝒩 := by
  have hbesTop : f ∈ besovP p s ⊤ := by
    rw [mem_besovP_iff] at hbes ⊢
    refine ⟨hbes.1, lt_of_le_of_lt ?_ hbes.2⟩
    rw [lqNorm, if_pos rfl]
    exact iSup_le_lq hq _
  obtain ⟨C0, C1, hC0, hC1, n0, hApp⟩ := hJ f hf hbesTop
  set R : ℝ := (⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|).toReal with hRdef
  set r1 : ℕ := max n0 ⌈4 * (R + 1)⌉₊ with hr1def
  -- `j ≥ r1` dá um aproximante `g ∈ Σ^H_{2^j}` com erro controlado
  have hJj : ∀ j : ℕ, r1 ≤ j → ∃ g ∈ Pendencias.Agenda.Sigma H (2 ^ j),
      eLpNorm (f - g) p vol01 ≤ ENNReal.ofReal C0 * wtP p (1 / (2 : ℝ) ^ j) f +
        ENNReal.ofReal C1 * ENNReal.ofReal (R + 1) / (H (2 ^ j) : ℝ≥0∞) := by
    intro j hj
    have hlt : j < 2 ^ j := Nat.lt_two_pow_self
    have hn0 : n0 ≤ j := le_trans (le_max_left _ _) hj
    have hc4 : ⌈4 * (R + 1)⌉₊ ≤ j := le_trans (le_max_right _ _) hj
    have h4 : 4 * (R + 1) ≤ ((2 ^ j : ℕ) : ℝ) := by
      have h1 := Nat.le_ceil (4 * (R + 1))
      have h2 : ((⌈4 * (R + 1)⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hc4
      have h3 : (j : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hlt.le
      linarith
    have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; rfl
    have hH := hHlow (2 ^ j) Nat.one_le_two_pow
    rw [hcast] at hH h4
    have hb : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hNs : ((2 : ℝ) ^ j) ≤ ((2 : ℝ) ^ j) ^ (max 1 s) := by
      calc (2 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ((2 : ℝ) ^ j) ^ (max 1 s) :=
            Real.rpow_le_rpow_of_exponent_le hb (le_max_left _ _)
    have h32 : 32 * (R + 1) ≤ 8 * ((2 : ℝ) ^ j) ^ (max 1 s) := by linarith
    have hthr : (H (2 ^ j) : ℝ) ≥ max (8 * ((2 : ℝ) ^ j) ^ (max 1 s)) (32 * (R + 1)) :=
      max_le (le_trans (le_refl _) hH) (le_trans h32 hH)
    obtain ⟨g, hg, hD⟩ := hApp j (le_trans hn0 hlt.le) (H (2 ^ j)) hthr
    exact ⟨g, classNH_subset_sigma H (2 ^ j) hg, hD⟩
  -- constante de escala `e` com `c ≤ 2^e`
  set e : ℕ := ⌈c⌉₊ with hedef
  have hce : c ≤ (2 : ℝ) ^ e := by
    have h1 : c ≤ (e : ℝ) := Nat.le_ceil c
    have h2 : (e : ℝ) < (2 : ℝ) ^ e := by exact_mod_cast Nat.lt_two_pow_self
    linarith
  set E : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ ((e : ℝ) * s)) with hEdef
  have hE : E ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc1 : (1 : ℝ≥0∞) + 5 * ENNReal.ofReal C0 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨by norm_num, ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩
  have hc2 : (5 : ℝ≥0∞) * ENNReal.ofReal C1 * ENNReal.ofReal (R + 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  -- cauda em ℓ^q
  have hT1 : lqNorm q (fun k : ℕ => if e ≤ k then
      (fun m : ℕ => besovSeq p s f (m + 1)) (k - e) else 0) < ⊤ :=
    lt_of_le_of_lt (lq_tail_le hq _ e)
      (lt_of_le_of_lt (lq_shift_le hq (besovSeq p s f)) ((mem_besovP_iff p s q f).1 hbes).2)
  have hT2 : lqNorm q (fun k : ℕ => if e ≤ k then
      ENNReal.ofReal ((2 : ℝ) ^ (((k - e + 1 : ℕ) : ℝ) * s)) /
        (H (2 ^ (k - e + 1)) : ℝ≥0∞) else 0) < ⊤ :=
    lt_of_le_of_lt (lq_tail_le hq (fun m : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((m + 1 : ℕ) : ℝ) * s)) /
      (H (2 ^ (m + 1)) : ℝ≥0∞)) e) hW
  set X : ℕ → ℝ≥0∞ := fun k => E * ((1 + 5 * ENNReal.ofReal C0) *
      (if e ≤ k then (fun m : ℕ => besovSeq p s f (m + 1)) (k - e) else 0) +
      (5 * ENNReal.ofReal C1 * ENNReal.ofReal (R + 1)) *
        (if e ≤ k then ENNReal.ofReal ((2 : ℝ) ^ (((k - e + 1 : ℕ) : ℝ) * s)) /
          (H (2 ^ (k - e + 1)) : ℝ≥0∞) else 0)) with hXdef
  have hX : lqNorm q X < ⊤ :=
    lq_const_mul_lt_top hq hE (lq_add_lt_top hq (lq_const_mul_lt_top hq hc1 hT1)
      (lq_const_mul_lt_top hq hc2 hT2))
  -- majoração termo a termo para `k ≥ e + r1`
  have hpt : ∀ k : ℕ, e + r1 ≤ k → stratSeq p s 𝒩 f k ≤ X k := by
    intro k hk
    have hek : e ≤ k := by omega
    have hr : r1 ≤ k - e + 1 := by omega
    obtain ⟨g, hg, hD⟩ := hJj (k - e + 1) hr
    have hgm : Measurable g := measurable_sigma hg
    -- índices: n = 2^m com m = k - e + 1, e M = 2^{k+1} = 2^e · n
    have hmpos : 0 < 2 ^ (k - e + 1) := Nat.two_pow_pos _
    have hnM : 2 ^ (k - e + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hnat : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ e * ((2 ^ (k - e + 1) : ℕ) : ℝ) := by
      push_cast
      rw [← pow_add]
      congr 1
      omega
    -- o aproximante está em 𝒩_{2^{k+1}}, porque ⌈c n⌉ ≤ 2^{k+1}
    have hcle : ⌈c * ((2 ^ (k - e + 1) : ℕ) : ℝ)⌉₊ ≤ 2 ^ (k + 1) := by
      apply Nat.ceil_le.2
      rw [hnat]
      exact mul_le_mul_of_nonneg_right hce (Nat.cast_nonneg _)
    have hgN : g ∈ 𝒩 (2 ^ (k + 1)) :=
      fam_mono 𝒩 hnest hcle (hcont (2 ^ (k - e + 1)) hg)
    have hR := realP_le_of_approx' hp hf hmpos hnM hgN hgm hD
    have hcast : ((2 ^ (k - e + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k - e + 1) := by push_cast; rfl
    rw [hcast] at hR
    -- desdobramento do peso: 2^{(k+1)s} = E · 2^{(k-e+1)s}
    have hexp : ((k + 1 : ℕ) : ℝ) = (e : ℝ) + ((k - e + 1 : ℕ) : ℝ) := by
      rw [show k + 1 = e + (k - e + 1) by omega, Nat.cast_add]
    have hsplit : ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) =
        E * ENNReal.ofReal ((2 : ℝ) ^ (((k - e + 1 : ℕ) : ℝ) * s)) := by
      rw [hEdef, hexp, add_mul, Real.rpow_add (by norm_num), ENNReal.ofReal_mul (by positivity)]
    calc stratSeq p s 𝒩 f k
        = ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
            realP p 𝒩 (2 ^ (k + 1)) f := rfl
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
            (wtP p (1 / (2 : ℝ) ^ (k - e + 1)) f +
              5 * (ENNReal.ofReal C0 * wtP p (1 / (2 : ℝ) ^ (k - e + 1)) f +
                ENNReal.ofReal C1 * ENNReal.ofReal (R + 1) /
                  (H (2 ^ (k - e + 1)) : ℝ≥0∞))) :=
          mul_le_mul_left' hR _
      _ = X k := by
          rw [hsplit, hXdef]
          simp only [if_pos hek, besovSeq, div_eq_mul_inv]
          ring
  have hfin : ∀ k : ℕ, stratSeq p s 𝒩 f k ≠ ⊤ := fun k =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_lt (realP_lt_top_gen hp 𝒩 _ (h0 _) ((mem_besovP_iff p s q f).1 hbes).1))
  have hlq : lqNorm q (stratSeq p s 𝒩 f) < ⊤ :=
    lq_of_eventually_le hq (k1 := e + r1) hfin hX (fun k hk => hpt k hk)
  exact (mem_stratumP_iff p s q 𝒩 f).2 ⟨((mem_besovP_iff p s q f).1 hbes).1, hlq⟩

/-- **Conjectura 2 (forma bilateral)**: sob `J_p` e a família `𝒩` com elementos mensuráveis,
`f ∈ B^s_{p,q}` se e só se `f ∈ R^s_q(𝒩)`, para `f` mensurável. -/
theorem stability_iff_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    {q : ℝ≥0∞} (hq : 0 < q) (H : ℕ → ℕ)
    (hHlow : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤ (H N : ℝ))
    (hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
      (H (2 ^ (k + 1)) : ℝ≥0∞)) < ⊤)
    (𝒩 : ℕ → Set (ℝ → ℝ)) (h0 : ∀ N, (0 : ℝ → ℝ) ∈ 𝒩 N)
    (hnest : ∀ N, 𝒩 N ⊆ 𝒩 (N + 1))
    (hm𝒩 : ∀ N, ∀ g ∈ 𝒩 N, Measurable g)
    {c : ℝ} (hc : 1 ≤ c) (hcont : ∀ N, Pendencias.Agenda.Sigma H N ⊆ 𝒩 ⌈c * N⌉₊)
    {f : ℝ → ℝ} (hf : Measurable f) :
    f ∈ besovP p s q ↔ f ∈ stratumP p s q 𝒩 :=
  ⟨fun hbes => besov_subset_stratum_fam hp hJ hq H hHlow hW 𝒩 h0 hnest hc hcont hf hbes,
    fun h => stratum_subset_besov_conn hp 𝒩 hm𝒩 s q hq hf h⟩

/-- **Conjectura 2, caso `q = ∞`, agenda `H_{s,0}`**, a partir de `J_p`. -/
theorem conj2_endpoint_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    (𝒩 : ℕ → Set (ℝ → ℝ)) (h0 : ∀ N, (0 : ℝ → ℝ) ∈ 𝒩 N)
    (hnest : ∀ N, 𝒩 N ⊆ 𝒩 (N + 1)) (hm𝒩 : ∀ N, ∀ g ∈ 𝒩 N, Measurable g)
    {c : ℝ} (hc : 1 ≤ c) (hcont : ∀ N, Pendencias.Agenda.Sigma (Pendencias.Agenda.Hsk s 0) N ⊆
      𝒩 ⌈c * N⌉₊)
    {f : ℝ → ℝ} (hf : Measurable f) :
    f ∈ besovP p s ⊤ ↔ f ∈ stratumP p s ⊤ 𝒩 := by
  have hH : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤
      (Pendencias.Agenda.Hsk s 0 N : ℝ) := fun N hN => Hsk_low (le_refl 0) N hN
  have hW : lqNorm ⊤ (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
      (Pendencias.Agenda.Hsk s 0 (2 ^ (k + 1)) : ℝ≥0∞)) < ⊤ := by
    rw [lqNorm, if_pos rfl]
    exact lt_of_le_of_lt (iSup_le fun k => weight_bdd _ hH k) ENNReal.ofReal_lt_top
  exact stability_iff_of_J hp hJ ENNReal.zero_lt_top (Pendencias.Agenda.Hsk s 0) hH hW 𝒩 h0
    hnest hm𝒩 hc hcont hf

/-- **Conjectura 2, caso `0 < q < ∞`, `s < 1`** (subcrítico), agenda `H_{s,0}`. -/
theorem conj2_subcritical_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    (hs : s < 1) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤)
    (𝒩 : ℕ → Set (ℝ → ℝ)) (h0 : ∀ N, (0 : ℝ → ℝ) ∈ 𝒩 N)
    (hnest : ∀ N, 𝒩 N ⊆ 𝒩 (N + 1)) (hm𝒩 : ∀ N, ∀ g ∈ 𝒩 N, Measurable g)
    {c : ℝ} (hc : 1 ≤ c) (hcont : ∀ N, Pendencias.Agenda.Sigma (Pendencias.Agenda.Hsk s 0) N ⊆
      𝒩 ⌈c * N⌉₊)
    {f : ℝ → ℝ} (hf : Measurable f) :
    f ∈ besovP p s q ↔ f ∈ stratumP p s q 𝒩 := by
  have hH : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤
      (Pendencias.Agenda.Hsk s 0 N : ℝ) := fun N hN => Hsk_low (le_refl 0) N hN
  have hmax : max 1 s = 1 := max_eq_left hs.le
  have hH1 : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (1 : ℝ) ≤
      (Pendencias.Agenda.Hsk s 0 N : ℝ) := by
    intro N hN
    have := hH N hN
    rwa [hmax] at this
  have hneg : s - 1 < 0 := by linarith
  have hρ1 : (2 : ℝ) ^ (s - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  have hρ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (s - 1) := by positivity
  have hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
      (Pendencias.Agenda.Hsk s 0 (2 ^ (k + 1)) : ℝ≥0∞)) < ⊤ :=
    lq_of_geom_le hq0 hqt (C := (2 : ℝ) ^ (s - 1) / 8) (ρ := (2 : ℝ) ^ (s - 1))
      (by positivity) hρ0 hρ1 (fun k => weight_geom _ hs hH1 k)
  exact stability_iff_of_J hp hJ hq0 (Pendencias.Agenda.Hsk s 0) hH hW 𝒩 h0 hnest hm𝒩 hc
    hcont hf

/-- **Conjectura 2, caso `0 < q < ∞`, `1 ≤ s`, `κ q > 1`** (crítico), agenda `H_{s,κ}`. -/
theorem conj2_critical_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    (hs : 1 ≤ s) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) {κ : ℝ} (hκ : 0 ≤ κ)
    (hκq : 1 < κ * q.toReal)
    (𝒩 : ℕ → Set (ℝ → ℝ)) (h0 : ∀ N, (0 : ℝ → ℝ) ∈ 𝒩 N)
    (hnest : ∀ N, 𝒩 N ⊆ 𝒩 (N + 1)) (hm𝒩 : ∀ N, ∀ g ∈ 𝒩 N, Measurable g)
    {c : ℝ} (hc : 1 ≤ c) (hcont : ∀ N, Pendencias.Agenda.Sigma (Pendencias.Agenda.Hsk s κ) N ⊆
      𝒩 ⌈c * N⌉₊)
    {f : ℝ → ℝ} (hf : Measurable f) :
    f ∈ besovP p s q ↔ f ∈ stratumP p s q 𝒩 := by
  have hH : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤
      (Pendencias.Agenda.Hsk s κ N : ℝ) := fun N hN => Hsk_low hκ N hN
  have hD : 0 ≤ 1 / 8 * (Real.log 2) ^ (-κ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _)
  have hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
      (Pendencias.Agenda.Hsk s κ (2 ^ (k + 1)) : ℝ≥0∞)) < ⊤ :=
    lq_of_poly_le hq0 hqt hD hκq (fun k => weight_poly hs hκ k)
  exact stability_iff_of_J hp hJ hq0 (Pendencias.Agenda.Hsk s κ) hH hW 𝒩 h0 hnest hm𝒩 hc
    hcont hf

/-- **Conjectura 2 com a agenda `H̃_{s,η}`**, `0 < q < ∞`, `η > 0`, a partir de `J_p`. -/
theorem conj2_tilde_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) {η : ℝ} (hη : 0 < η)
    (𝒩 : ℕ → Set (ℝ → ℝ)) (h0 : ∀ N, (0 : ℝ → ℝ) ∈ 𝒩 N)
    (hnest : ∀ N, 𝒩 N ⊆ 𝒩 (N + 1)) (hm𝒩 : ∀ N, ∀ g ∈ 𝒩 N, Measurable g)
    {c : ℝ} (hc : 1 ≤ c) (hcont : ∀ N, Pendencias.Agenda.Sigma
      (fun N => Pendencias.Jackson.HtilK 0 0 s η N) N ⊆ 𝒩 ⌈c * N⌉₊)
    {f : ℝ → ℝ} (hf : Measurable f) :
    f ∈ besovP p s q ↔ f ∈ stratumP p s q 𝒩 := by
  have hH : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤
      (Pendencias.Jackson.HtilK 0 0 s η N : ℝ) := fun N hN => Htil_low hη.le N hN
  have ha : s < max 1 (s + η) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hH' : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 (s + η)) ≤
      (Pendencias.Jackson.HtilK 0 0 s η N : ℝ) := by
    intro N hN
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h1 : (N : ℝ) ^ (max 1 (s + η)) ≤ ((N : ℝ) + 1) ^ (max 1 (s + η)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith)
        (le_trans zero_le_one (le_max_left _ _))
    have h2 := Htil_real_ge s η N
    linarith
  have hneg : s - max 1 (s + η) < 0 := by linarith
  have hρ1 : (2 : ℝ) ^ (s - max 1 (s + η)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  have hρ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (s - max 1 (s + η)) := by positivity
  have hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
      (Pendencias.Jackson.HtilK 0 0 s η (2 ^ (k + 1)) : ℝ≥0∞)) < ⊤ :=
    lq_of_geom_le hq0 hqt (C := (2 : ℝ) ^ (s - max 1 (s + η)) / 8)
      (ρ := (2 : ℝ) ^ (s - max 1 (s + η))) (by positivity) hρ0 hρ1
      (fun k => weight_geom _ ha hH' k)
  exact stability_iff_of_J hp hJ hq0 (fun N => Pendencias.Jackson.HtilK 0 0 s η N) hH hW 𝒩 h0
    hnest hm𝒩 hc hcont hf

/-! ## Enunciado `Conj2Stability` de cada regime, como consequência de `J_p` -/

theorem conj2Stability_endpoint_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    (c : ℝ) : Conj2Stability p s ⊤ (Pendencias.Agenda.Hsk s 0) c :=
  fun hc 𝒩 h0 hnest hm𝒩 hcont f hf => conj2_endpoint_of_J hp hJ 𝒩 h0 hnest hm𝒩 hc hcont hf

theorem conj2Stability_subcritical_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    (hs : s < 1) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) (c : ℝ) :
    Conj2Stability p s q (Pendencias.Agenda.Hsk s 0) c :=
  fun hc 𝒩 h0 hnest hm𝒩 hcont f hf =>
    conj2_subcritical_of_J hp hJ hs hq0 hqt 𝒩 h0 hnest hm𝒩 hc hcont hf

theorem conj2Stability_critical_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    (hs : 1 ≤ s) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) {κ : ℝ} (hκ : 0 ≤ κ)
    (hκq : 1 < κ * q.toReal) (c : ℝ) :
    Conj2Stability p s q (Pendencias.Agenda.Hsk s κ) c :=
  fun hc 𝒩 h0 hnest hm𝒩 hcont f hf =>
    conj2_critical_of_J hp hJ hs hq0 hqt hκ hκq 𝒩 h0 hnest hm𝒩 hc hcont hf

theorem conj2Stability_tilde_of_J {p : ℝ≥0∞} (hp : 1 ≤ p) {s : ℝ} (hJ : HypJp p s)
    {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) {η : ℝ} (hη : 0 < η) (c : ℝ) :
    Conj2Stability p s q (fun N => Pendencias.Jackson.HtilK 0 0 s η N) c :=
  fun hc 𝒩 h0 hnest hm𝒩 hcont f hf =>
    conj2_tilde_of_J hp hJ hq0 hqt hη 𝒩 h0 hnest hm𝒩 hc hcont hf

end FormalizacaoStab
