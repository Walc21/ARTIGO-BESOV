import Formalizacao.LpJackson2
import Formalizacao.Theorems
import Formalizacao.Stability

/-!
# M8: as Conjecturas 1 e 2 são teoremas

Com `hypJp_of_lt`, a hipótese `J_p` deixa de ser premissa. Para `1 ≤ p < ∞` e `1/p < s`, valem
as igualdades `B^s_{p,q} = R^s_q(Σ^H)` (Conjectura 1) e a estabilidade por inclusão de redes
(Conjectura 2), em cada regime de parâmetros, para funções mensuráveis.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoLp FormalizacaoThm FormalizacaoStab

namespace FormalizacaoJ

/-- `J_p` para `p ∈ [1, ∞)` e `1/p < s`, com `p : ℝ≥0∞` -/
theorem hypJp_of_lt' {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {s : ℝ} (hs : 1 / p.toReal < s) :
    HypJp p s := by
  have h1 : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp
    simpa using this
  have := hypJp_of_lt h1 hs
  rwa [ENNReal.ofReal_toReal hpt] at this

/-- **Conjectura 1, `q = ∞`.** -/
theorem conj1_endpoint {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {s : ℝ} (hs : 1 / p.toReal < s) :
    Conj1Endpoint p s :=
  conj1_endpoint_of_J hp (hypJp_of_lt' hp hpt hs)

/-- **Conjectura 1, `0 < q < ∞`, `s < 1`.** -/
theorem conj1_subcritical {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {s : ℝ}
    (hs : 1 / p.toReal < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) :
    Conj1Subcritical p s q :=
  conj1_subcritical_of_J hp (hypJp_of_lt' hp hpt hs) hs1 hq0 hqt

/-- **Conjectura 1, `0 < q < ∞`, `1 ≤ s`, `κ q > 1`.** -/
theorem conj1_critical {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {s : ℝ}
    (hs : 1 / p.toReal < s) (hs1 : 1 ≤ s) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) {κ : ℝ}
    (hκ : 0 ≤ κ) (hκq : 1 < κ * q.toReal) :
    Conj1Critical p s q κ :=
  conj1_critical_of_J hp (hypJp_of_lt' hp hpt hs) hs1 hq0 hqt hκ hκq

/-- **Conjectura 1 com a agenda alternativa `H̃_{s,η}`**, com `1/p < s < 2` como no artigo. -/
theorem conj1_tilde {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {s : ℝ} (hs : 1 / p.toReal < s)
    (_hs2 : s < 2) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) {η : ℝ} (hη : 0 < η) (f : ℝ → ℝ)
    (hf : Measurable f) :
    f ∈ besovP p s q ↔ f ∈ stratumP p s q (Pendencias.Agenda.Sigma
      (fun N => Pendencias.Jackson.HtilK 0 0 s η N)) :=
  conj1_tilde_of_J hp (hypJp_of_lt' hp hpt hs) hq0 hqt hη f hf

/-- **Conjectura 2, `q = ∞`.** -/
theorem conj2_endpoint {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {s : ℝ} (hs : 1 / p.toReal < s)
    (c : ℝ) : Conj2Stability p s ⊤ (Pendencias.Agenda.Hsk s 0) c :=
  conj2Stability_endpoint_of_J hp (hypJp_of_lt' hp hpt hs) c

/-- **Conjectura 2, `0 < q < ∞`, `s < 1`.** -/
theorem conj2_subcritical {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {s : ℝ}
    (hs : 1 / p.toReal < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) (c : ℝ) :
    Conj2Stability p s q (Pendencias.Agenda.Hsk s 0) c :=
  conj2Stability_subcritical_of_J hp (hypJp_of_lt' hp hpt hs) hs1 hq0 hqt c

/-- **Conjectura 2, `0 < q < ∞`, `1 ≤ s`, `κ q > 1`.** -/
theorem conj2_critical {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {s : ℝ}
    (hs : 1 / p.toReal < s) (hs1 : 1 ≤ s) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) {κ : ℝ}
    (hκ : 0 ≤ κ) (hκq : 1 < κ * q.toReal) (c : ℝ) :
    Conj2Stability p s q (Pendencias.Agenda.Hsk s κ) c :=
  conj2Stability_critical_of_J hp (hypJp_of_lt' hp hpt hs) hs1 hq0 hqt hκ hκq c

/-- **Conjectura 2 com `H̃_{s,η}`**, com `1/p < s < 2` como no artigo. -/
theorem conj2_tilde {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {s : ℝ} (hs : 1 / p.toReal < s)
    (_hs2 : s < 2) {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) {η : ℝ} (hη : 0 < η) (c : ℝ) :
    Conj2Stability p s q (fun N => Pendencias.Jackson.HtilK 0 0 s η N) c :=
  conj2Stability_tilde_of_J hp (hypJp_of_lt' hp hpt hs) hq0 hqt hη c

end FormalizacaoJ
