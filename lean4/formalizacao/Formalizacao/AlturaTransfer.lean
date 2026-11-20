import Formalizacao.AlturaNecessity

/-!
# Transferência entre erro e realização; necessidade com realização (auditoria, Partes II e VI)

* `bestError_le_realP`: `e_N(f) ≤ R_N(f)` (cota inferior: a realização não é menor que o erro).
* `realP_le_of_member`: `R_N(f) ≤ ω_p(f,1/N) + 5 ‖f - g‖_p` para todo `g ∈ G_N` (cota superior).
* `realP_le_bestError_add`: `R_N(f) ≤ ω_p(f,1/N) + 5 e_N(f)` (ínfimo sobre `g`).

Consequência: uma hipótese uniforme sobre a realização implica a mesma hipótese sobre o erro, e
portanto as necessidades de `AlturaNecessity` valem também para `R_N`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoAltura

open FormalizacaoLp FormalizacaoLow

/-- `e_N(f) ≤ R_N(f)`: o erro é o ínfimo de `‖f-g‖`, e `R_N` soma `ω(g)` a cada termo. -/
lemma bestError_le_realP (p : ℝ≥0∞) (G : ℕ → Set (ℝ → ℝ)) (N : ℕ) (f : ℝ → ℝ) :
    (⨅ g ∈ G N, distP p f g) ≤ realP p G N f :=
  le_iInf₂ fun g hg => (iInf₂_le g hg).trans le_self_add

/-- `ω_p(g,t) ≤ ω_p(f,t) + 4‖f-g‖_p` para funções mensuráveis. -/
lemma wtP_shift_le {p : ℝ≥0∞} (hp : 1 ≤ p) (t : ℝ) {f g : ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) : wtP p t g ≤ wtP p t f + 4 * distP p f g := by
  have hgf : g = (g - f) + f := by funext x; simp
  have hsub : wtP p t g ≤ wtP p t (g - f) + wtP p t f := by
    conv_lhs => rw [hgf]
    exact wtP_add_le hp t (hg.sub hf) hf
  have h4 : wtP p t (g - f) ≤ 4 * distP p f g := by
    refine (wtP_le_four hp t (hg.sub hf)).trans ?_
    unfold distP
    have e : (fun a => g a - f a) = -(f - g) := by
      funext x; simp only [Pi.neg_apply, Pi.sub_apply]; ring
    rw [e, eLpNorm_neg]
  calc wtP p t g ≤ wtP p t (g - f) + wtP p t f := hsub
    _ ≤ 4 * distP p f g + wtP p t f := add_le_add_left h4 _
    _ = wtP p t f + 4 * distP p f g := by ring

/-- Cota superior por um membro: `R_N(f) ≤ ω(f,1/N) + 5‖f-g‖` para `g ∈ G_N`. -/
lemma realP_le_of_member {p : ℝ≥0∞} (hp : 1 ≤ p) (G : ℕ → Set (ℝ → ℝ)) (N : ℕ)
    {f : ℝ → ℝ} (hf : Measurable f) {g : ℝ → ℝ} (hg : g ∈ G N) (hgm : Measurable g) :
    realP p G N f ≤ wtP p (1 / (N : ℝ)) f + 5 * distP p f g := by
  have h1 : realP p G N f ≤ distP p f g + wtP p (1 / (N : ℝ)) g :=
    iInf₂_le g hg
  have h2 := wtP_shift_le hp (1 / (N : ℝ)) hf hgm
  calc realP p G N f ≤ distP p f g + wtP p (1 / (N : ℝ)) g := h1
    _ ≤ distP p f g + (wtP p (1 / (N : ℝ)) f + 4 * distP p f g) := add_le_add le_rfl h2
    _ = wtP p (1 / (N : ℝ)) f + 5 * distP p f g := by ring

/-- Cota superior pelo erro: `R_N(f) ≤ ω(f,1/N) + 5 e_N(f)`. -/
lemma realP_le_bestError_add {p : ℝ≥0∞} (hp : 1 ≤ p) (G : ℕ → Set (ℝ → ℝ)) (N : ℕ)
    {f : ℝ → ℝ} (hf : Measurable f) (hG : ∀ g ∈ G N, Measurable g) :
    realP p G N f ≤ wtP p (1 / (N : ℝ)) f + 5 * ⨅ g ∈ G N, distP p f g := by
  have hkey : realP p G N f ≤ ⨅ g ∈ G N, (wtP p (1 / (N : ℝ)) f + 5 * distP p f g) :=
    le_iInf₂ fun g hg => realP_le_of_member hp G N hf hg (hG g hg)
  refine hkey.trans (le_of_eq ?_)
  simp_rw [ENNReal.mul_iInf_of_ne (show (5 : ℝ≥0∞) ≠ 0 by norm_num)
    (show (5 : ℝ≥0∞) ≠ ⊤ by norm_num), ENNReal.add_iInf]

/-! ## Necessidade com a realização `R_N` -/

/-- Versão com realização da necessidade geométrica (`R_N ≥ e_N`). -/
theorem geometric_necessity_realP {p q : ℝ≥0∞} {s : ℝ} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (hq0 : 0 < q) (hs : 0 < s) (hs2 : s < 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (C : ℝ) (N h : ℕ), 0 < C → 1 ≤ N → 2 ≤ h →
      (∀ f : ℝ → ℝ, Measurable f → besovNorm p s q f ≤ 1 →
        realP p (fun M => Pendencias.Agenda.Sigma (fun _ => h) M) N f ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-s))) →
      (c / C) ^ s⁻¹ * (N : ℝ) ≤ (h : ℝ) := by
  obtain ⟨c, hc, hn⟩ := geometric_necessity (q := q) hp1 hpt hq0 hs hs2
  refine ⟨c, hc, fun C N h hC hN hh hR => hn C N h hC hN hh ?_⟩
  intro f hf hb
  exact (bestError_le_realP p (fun M => Pendencias.Agenda.Sigma (fun _ => h) M) N f).trans
    (hR f hf hb)

/-- Versão com realização da necessidade no regime de inclinação. -/
theorem slope_necessity_realP {p q : ℝ≥0∞} {s : ℝ} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (hq0 : 0 < q) (hs : 0 < s) (hs2 : s < 2) (hsp : s ≤ p.toReal⁻¹) :
    ∃ c : ℝ, 0 < c ∧ ∀ (C : ℝ) (N h : ℕ), 0 < C → 1 ≤ N → 2 ≤ h →
      (∀ f : ℝ → ℝ, Measurable f → besovNorm p s q f ≤ 1 →
        realP p (fun M => Pendencias.Agenda.Sigma (fun _ => h) M) N f ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-s))) →
      (c / C) ^ (s / (1 + (p.toReal⁻¹ - s)))⁻¹ * (N : ℝ) ^ (1 + (p.toReal⁻¹ - s)) ≤ (h : ℝ) := by
  obtain ⟨c, hc, hn⟩ := slope_necessity (q := q) hp1 hpt hq0 hs hs2 hsp
  refine ⟨c, hc, fun C N h hC hN hh hR => hn C N h hC hN hh ?_⟩
  intro f hf hb
  exact (bestError_le_realP p (fun M => Pendencias.Agenda.Sigma (fun _ => h) M) N f).trans
    (hR f hf hb)

/-- Versão com realização do piso aritmético. -/
theorem arithmetic_necessity_realP {p q : ℝ≥0∞} {s : ℝ} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (hq0 : 0 < q) (hs : 0 < s) {C : ℝ} (hC : 0 < C) {N h : ℕ} (hN : 1 ≤ N) (hh : 1 ≤ h)
    (hR : ∀ f : ℝ → ℝ, Measurable f → besovNorm p s q f ≤ 1 →
      realP p (fun M => Pendencias.Agenda.Sigma (fun _ => h) M) N f ≤
        ENNReal.ofReal (C * (N : ℝ) ^ (-s))) :
    (1 / (2 * C)) * (N : ℝ) ^ s ≤ (h : ℝ) :=
  arithmetic_necessity hp1 hpt hq0 hs hC hN hh (fun f hf hb =>
    (bestError_le_realP p (fun M => Pendencias.Agenda.Sigma (fun _ => h) M) N f).trans
      (hR f hf hb))

end FormalizacaoAltura
