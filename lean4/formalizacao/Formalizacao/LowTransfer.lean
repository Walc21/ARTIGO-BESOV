import Formalizacao.LowJackson2
import Formalizacao.Stability

/-!
# Regimes `s ≤ 1/p`, parte 6: transferência (`Proposição lp:thm:low-transfer`)

Dada a família aninhada `𝒩`, contendo `0`, com `Σ^H_N ⊆ 𝒩_{⌈cN⌉}`, e uma quantização
`Q(2^r) = 2^{r + m r}` tal que
* (deslocamento) `8 (K Λ_r + 1) 2^{r + m r} ≤ H(2^{r+e0})` para todo `r ≥ 1` (com `e0` dependendo
  de `K`) e
* (peso) `k ↦ 2^{(k+1)s} / (2 · 2^{(k+1)+m(k+1)})` pertence a `ℓ^q`,

vale `B^s_{p,q} ⊆ R^s_q(𝒩)`, para `f` mensurável e `s ≤ 1/p`.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoLp FormalizacaoLq FormalizacaoRed FormalizacaoStab

namespace FormalizacaoLow

theorem besov_subset_stratum_low_core {p : ℝ} (hp : 1 ≤ p) {s : ℝ} (hs : s ≤ 1 / p)
    {q : ℝ≥0∞} (hq : 0 < q) (H : ℕ → ℕ) (m : ℕ → ℕ)
    (hshift : ∀ K : ℝ, 1 ≤ K → ∃ e0 : ℕ, ∀ r : ℕ, 1 ≤ r →
      8 * (K * Lam p s q r + 1) * 2 ^ (r + m r) ≤ (H (2 ^ (r + e0)) : ℝ))
    (hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
      ENNReal.ofReal (1 / (2 * 2 ^ ((k + 1) + m (k + 1))))) < ⊤)
    (𝒩 : ℕ → Set (ℝ → ℝ)) (h0 : ∀ N, (0 : ℝ → ℝ) ∈ 𝒩 N)
    (hnest : ∀ N, 𝒩 N ⊆ 𝒩 (N + 1))
    {c : ℝ} (hc : 1 ≤ c) {ε : ℕ → ℝ≥0∞}
    (hEps : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
      ε (2 ^ (k + 1))) < ⊤)
    (happrox : ∀ N, ∀ g ∈ Pendencias.Agenda.Sigma H N,
      ∃ g' ∈ 𝒩 ⌈c * N⌉₊, Measurable g' ∧ eLpNorm (g - g') (ENNReal.ofReal p) vol01 ≤ ε N)
    {f : ℝ → ℝ} (hf : Measurable f) (hbes : f ∈ besovP (ENNReal.ofReal p) s q) :
    f ∈ stratumP (ENNReal.ofReal p) s q 𝒩 := by
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨CW, K, hCW, hK1, hApp⟩ := jackson_low hp hs hq hf hbes
  obtain ⟨e0, hshift'⟩ := hshift K hK1
  set e1 : ℕ := ⌈c⌉₊ with he1def
  have hce : c ≤ (2 : ℝ) ^ e1 := by
    have h1 : c ≤ (e1 : ℝ) := Nat.le_ceil c
    have h2 : (e1 : ℝ) < (2 : ℝ) ^ e1 := by exact_mod_cast Nat.lt_two_pow_self
    linarith
  set E : ℕ := e1 + e0 with hEdef
  set Es : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ ((E : ℝ) * s)) with hEsdef
  have hEs : Es ≠ ⊤ := ENNReal.ofReal_ne_top
  set P : ℝ≥0∞ := ENNReal.ofReal p with hPdef
  have hc1 : (1 : ℝ≥0∞) + 5 * (9 * ENNReal.ofReal CW) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨by norm_num,
      ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)⟩
  have hc2 : (5 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hbes' := (mem_besovP_iff P s q f).1 hbes
  -- caudas em ℓ^q
  have hT1 : lqNorm q (fun k : ℕ => if E ≤ k then
      (fun j : ℕ => besovSeq P s f (j + 1)) (k - E) else 0) < ⊤ :=
    lt_of_le_of_lt (lq_tail_le hq _ E)
      (lt_of_le_of_lt (lq_shift_le hq (besovSeq P s f)) hbes'.2)
  have hT2 : lqNorm q (fun k : ℕ => if E ≤ k then
      (ENNReal.ofReal ((2 : ℝ) ^ (((k - E + 1 : ℕ) : ℝ) * s)) *
        ENNReal.ofReal (1 / (2 * 2 ^ ((k - E + 1) + m (k - E + 1))))) else 0) < ⊤ :=
    lt_of_le_of_lt (lq_tail_le hq (fun j : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * s)) *
      ENNReal.ofReal (1 / (2 * 2 ^ ((j + 1) + m (j + 1))))) E) hW
  set E1 : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ ((e1 : ℝ) * s)) with hE1def
  have hE1 : 5 * E1 ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hT3 : lqNorm q (fun k : ℕ => if e1 ≤ k then
      (ENNReal.ofReal ((2 : ℝ) ^ (((k - e1 + 1 : ℕ) : ℝ) * s)) * ε (2 ^ (k - e1 + 1))) else 0) < ⊤ :=
    lt_of_le_of_lt (lq_tail_le hq (fun j : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * s)) *
      ε (2 ^ (j + 1))) e1) hEps
  set X : ℕ → ℝ≥0∞ := fun k => Es * ((1 + 5 * (9 * ENNReal.ofReal CW)) *
      (if E ≤ k then (fun j : ℕ => besovSeq P s f (j + 1)) (k - E) else 0) +
      5 * (if E ≤ k then (ENNReal.ofReal ((2 : ℝ) ^ (((k - E + 1 : ℕ) : ℝ) * s)) *
        ENNReal.ofReal (1 / (2 * 2 ^ ((k - E + 1) + m (k - E + 1))))) else 0)) +
      (5 * E1) * (if e1 ≤ k then
        (ENNReal.ofReal ((2 : ℝ) ^ (((k - e1 + 1 : ℕ) : ℝ) * s)) * ε (2 ^ (k - e1 + 1))) else 0)
    with hXdef
  have hX : lqNorm q X < ⊤ :=
    lq_add_lt_top hq
      (lq_const_mul_lt_top hq hEs (lq_add_lt_top hq (lq_const_mul_lt_top hq hc1 hT1)
        (lq_const_mul_lt_top hq hc2 hT2)))
      (lq_const_mul_lt_top hq hE1 hT3)
  have hpt : ∀ k : ℕ, E ≤ k → stratSeq P s 𝒩 f k ≤ X k := by
    intro k hk
    set r : ℕ := k - E + 1 with hrdef
    have hr1 : 1 ≤ r := by omega
    have hre : r ≤ r + m r := Nat.le_add_right _ _
    obtain ⟨g, hg, hD⟩ := hApp r (r + m r) hr1 hre (H (2 ^ (r + e0))) (hshift' r hr1)
    have hgS : g ∈ Pendencias.Agenda.Sigma H (2 ^ (r + e0)) :=
      classNH_le_sigma H (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right r e0)) hg
    have hgm : Measurable g := measurable_sigma hgS
    obtain ⟨g', hg'c, hg'm, hg'err⟩ := happrox (2 ^ (r + e0)) g hgS
    have hkr : k + 1 = e1 + (r + e0) := by omega
    have hnat : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ e1 * ((2 ^ (r + e0) : ℕ) : ℝ) := by
      push_cast
      rw [← pow_add]
      congr 1
    have hcle : ⌈c * ((2 ^ (r + e0) : ℕ) : ℝ)⌉₊ ≤ 2 ^ (k + 1) := by
      apply Nat.ceil_le.2
      rw [hnat]
      exact mul_le_mul_of_nonneg_right hce (Nat.cast_nonneg _)
    have hgN : g' ∈ 𝒩 (2 ^ (k + 1)) := fam_mono 𝒩 hnest hcle hg'c
    have hD' : eLpNorm (f - g') (ENNReal.ofReal p) vol01 ≤
        (9 * ENNReal.ofReal CW * wtP P (1 / (2 : ℝ) ^ r) f +
          ENNReal.ofReal (1 / (2 * 2 ^ (r + m r)))) + ε (2 ^ (r + e0)) := by
      have hsplitf : f - g' = (f - g) + (g - g') := by
        ext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
      calc eLpNorm (f - g') (ENNReal.ofReal p) vol01
          = eLpNorm ((f - g) + (g - g')) (ENNReal.ofReal p) vol01 := by rw [hsplitf]
        _ ≤ eLpNorm (f - g) (ENNReal.ofReal p) vol01 + eLpNorm (g - g') (ENNReal.ofReal p) vol01 :=
            eLpNorm_add_le (hf.sub hgm).aestronglyMeasurable (hgm.sub hg'm).aestronglyMeasurable hP1
        _ ≤ _ := add_le_add hD hg'err
    have hnM : 2 ^ r ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmpos : 0 < 2 ^ r := Nat.two_pow_pos _
    have hR := realP_le_of_approx' hP1 hf hmpos hnM hgN hg'm hD'
    have hcast : ((2 ^ r : ℕ) : ℝ) = (2 : ℝ) ^ r := by push_cast; rfl
    rw [hcast] at hR
    have hexp : ((k + 1 : ℕ) : ℝ) = (E : ℝ) + (r : ℝ) := by
      have : k + 1 = E + r := by omega
      rw [this, Nat.cast_add]
    have hsplit : ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) =
        Es * ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) := by
      rw [hEsdef, hexp, add_mul, Real.rpow_add (by norm_num), ENNReal.ofReal_mul (by positivity)]
    have hEk : E ≤ k := hk
    have he1k : e1 ≤ k := by omega
    have hidx : k - e1 + 1 = r + e0 := by omega
    have hexp1 : ((k + 1 : ℕ) : ℝ) = (e1 : ℝ) + ((r + e0 : ℕ) : ℝ) := by
      have : k + 1 = e1 + (r + e0) := hkr
      rw [this, Nat.cast_add]
    have hsplit1 : ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) =
        E1 * ENNReal.ofReal ((2 : ℝ) ^ (((r + e0 : ℕ) : ℝ) * s)) := by
      rw [hE1def, hexp1, add_mul, Real.rpow_add (by norm_num), ENNReal.ofReal_mul (by positivity)]
    calc stratSeq P s 𝒩 f k
        = ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
            realP P 𝒩 (2 ^ (k + 1)) f := rfl
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
            (wtP P (1 / (2 : ℝ) ^ r) f +
              5 * ((9 * ENNReal.ofReal CW * wtP P (1 / (2 : ℝ) ^ r) f +
                ENNReal.ofReal (1 / (2 * 2 ^ (r + m r)))) + ε (2 ^ (r + e0)))) :=
          mul_le_mul_left' hR _
      _ = ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
            (wtP P (1 / (2 : ℝ) ^ r) f +
              5 * (9 * ENNReal.ofReal CW * wtP P (1 / (2 : ℝ) ^ r) f +
                ENNReal.ofReal (1 / (2 * 2 ^ (r + m r))))) +
          ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) * (5 * ε (2 ^ (r + e0))) := by
          ring
      _ = Es * ((1 + 5 * (9 * ENNReal.ofReal CW)) * besovSeq P s f r +
            5 * (ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) *
              ENNReal.ofReal (1 / (2 * 2 ^ (r + m r))))) +
          (5 * E1) * (ENNReal.ofReal ((2 : ℝ) ^ (((r + e0 : ℕ) : ℝ) * s)) *
            ε (2 ^ (r + e0))) := by
          have h1 : ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
              (wtP P (1 / (2 : ℝ) ^ r) f +
                5 * (9 * ENNReal.ofReal CW * wtP P (1 / (2 : ℝ) ^ r) f +
                  ENNReal.ofReal (1 / (2 * 2 ^ (r + m r))))) =
              Es * ((1 + 5 * (9 * ENNReal.ofReal CW)) * besovSeq P s f r +
                5 * (ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) *
                  ENNReal.ofReal (1 / (2 * 2 ^ (r + m r))))) := by
            rw [hsplit]
            simp only [besovSeq]
            ring
          have h2 : ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) * (5 * ε (2 ^ (r + e0))) =
              (5 * E1) * (ENNReal.ofReal ((2 : ℝ) ^ (((r + e0 : ℕ) : ℝ) * s)) *
                ε (2 ^ (r + e0))) := by
            rw [hsplit1]; ring
          rw [h1, h2]
      _ = X k := by
          rw [hXdef]
          simp only [if_pos hEk, if_pos he1k, besovSeq, hidx]
          rfl
  have hfin : ∀ k : ℕ, stratSeq P s 𝒩 f k ≠ ⊤ := fun k =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_lt (realP_lt_top_gen hP1 𝒩 _ (h0 _) hbes'.1))
  have hlq : lqNorm q (stratSeq P s 𝒩 f) < ⊤ :=
    lq_of_eventually_le hq (k1 := E) hfin hX (fun k hk => hpt k hk)
  exact (mem_stratumP_iff P s q 𝒩 f).2 ⟨hbes'.1, hlq⟩

/-- Transferência de baixa regularidade (`Proposição lp:thm:low-transfer`), com
`Σ^H_N ⊆ 𝒩_{⌈cN⌉}`: o caso `ε = 0` do núcleo. -/
theorem besov_subset_stratum_low {p : ℝ} (hp : 1 ≤ p) {s : ℝ} (hs : s ≤ 1 / p)
    {q : ℝ≥0∞} (hq : 0 < q) (H : ℕ → ℕ) (m : ℕ → ℕ)
    (hshift : ∀ K : ℝ, 1 ≤ K → ∃ e0 : ℕ, ∀ r : ℕ, 1 ≤ r →
      8 * (K * Lam p s q r + 1) * 2 ^ (r + m r) ≤ (H (2 ^ (r + e0)) : ℝ))
    (hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
      ENNReal.ofReal (1 / (2 * 2 ^ ((k + 1) + m (k + 1))))) < ⊤)
    (𝒩 : ℕ → Set (ℝ → ℝ)) (h0 : ∀ N, (0 : ℝ → ℝ) ∈ 𝒩 N)
    (hnest : ∀ N, 𝒩 N ⊆ 𝒩 (N + 1))
    {c : ℝ} (hc : 1 ≤ c) (hcont : ∀ N, Pendencias.Agenda.Sigma H N ⊆ 𝒩 ⌈c * N⌉₊)
    {f : ℝ → ℝ} (hf : Measurable f) (hbes : f ∈ besovP (ENNReal.ofReal p) s q) :
    f ∈ stratumP (ENNReal.ofReal p) s q 𝒩 := by
  have hEps : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
      (0 : ℝ≥0∞)) < ⊤ := by
    have hzero : (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) * (0 : ℝ≥0∞)) =
        fun _ => 0 := by funext _; simp
    rw [hzero]
    exact lq_finsupp_lt_top hq (k1 := 0) (fun _ _ => rfl) (fun _ => ENNReal.zero_ne_top)
  exact besov_subset_stratum_low_core hp hs hq H m hshift hW 𝒩 h0 hnest hc (ε := fun _ => 0) hEps
    (fun N g hg => ⟨g, hcont N hg, measurable_sigma hg, by simp⟩) hf hbes

/-- Transferência de baixa regularidade sob inclusão aproximada
(`Proposição lp:thm:low-approx-transfer`). -/
theorem besov_subset_stratum_low_approx {p : ℝ} (hp : 1 ≤ p) {s : ℝ} (hs : s ≤ 1 / p)
    {q : ℝ≥0∞} (hq : 0 < q) (H : ℕ → ℕ) (m : ℕ → ℕ)
    (hshift : ∀ K : ℝ, 1 ≤ K → ∃ e0 : ℕ, ∀ r : ℕ, 1 ≤ r →
      8 * (K * Lam p s q r + 1) * 2 ^ (r + m r) ≤ (H (2 ^ (r + e0)) : ℝ))
    (hW : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
      ENNReal.ofReal (1 / (2 * 2 ^ ((k + 1) + m (k + 1))))) < ⊤)
    (𝒩 : ℕ → Set (ℝ → ℝ)) (h0 : ∀ N, (0 : ℝ → ℝ) ∈ 𝒩 N)
    (hnest : ∀ N, 𝒩 N ⊆ 𝒩 (N + 1)) (hm𝒩 : ∀ N, ∀ g ∈ 𝒩 N, Measurable g)
    {c : ℝ} (hc : 1 ≤ c) {ε : ℕ → ℝ≥0∞}
    (hEps : lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
      ε (2 ^ (k + 1))) < ⊤)
    (happrox : ∀ N, ∀ g ∈ Pendencias.Agenda.Sigma H N,
      ∃ g' ∈ 𝒩 ⌈c * N⌉₊, eLpNorm (g - g') (ENNReal.ofReal p) vol01 ≤ ε N)
    {f : ℝ → ℝ} (hf : Measurable f) (hbes : f ∈ besovP (ENNReal.ofReal p) s q) :
    f ∈ stratumP (ENNReal.ofReal p) s q 𝒩 :=
  besov_subset_stratum_low_core hp hs hq H m hshift hW 𝒩 h0 hnest hc hEps
    (fun N g hg => by
      obtain ⟨g', hg'c, hg'err⟩ := happrox N g hg
      exact ⟨g', hg'c, hm𝒩 _ g' hg'c, hg'err⟩) hf hbes

end FormalizacaoLow
