import Formalizacao.AlturaCritical3

/-!
# Item (d) do Teorema lp:thm:critical-linear, restrito à bola de raio `B`

* Se `‖f‖* ≤ B`, então `f ∈ Rstr_{1/p,q}(H_B)` (agenda crítica dependente de `B`).
* Para toda `f` mensurável, `Rstr_{1/p,q}(H_B) ⊆ B^{1/p}_{p,q}` (vale para qualquer agenda).

Assim a bola de raio `B` fica contida em `Rstr(H_B)`, que fica contida em `B^{1/p}_{p,q}`;
não se afirma igualdade para agenda fixa.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoCrit4

open FormalizacaoCrit3 FormalizacaoLp FormalizacaoLow FormalizacaoRed

theorem critical_radius_ball_and_inclusion {p CW : ℝ} {q : ℝ≥0∞} (hp : 1 < p)
    (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW) (hq0 : 0 < q) (hqt : q ≠ ⊤)
    {B : ℝ} (hB : 1 ≤ B) :
    (∀ f : ℝ → ℝ, Measurable f →
        besovNorm (ENNReal.ofReal p) (1 / p) q f ≤ ENNReal.ofReal B →
        f ∈ stratumP (ENNReal.ofReal p) (1 / p) q
          (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M)) ∧
    (∀ f : ℝ → ℝ, Measurable f →
        f ∈ stratumP (ENNReal.ofReal p) (1 / p) q
          (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M) →
        f ∈ besovP (ENNReal.ofReal p) (1 / p) q) := by
  have hGm : ∀ N, ∀ g ∈ (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M) N,
      Measurable g :=
    fun N g hg => FormalizacaoLp.measurable_sigma hg
  refine ⟨fun f hf hbes => ?_, fun f hf hs => ?_⟩
  · have hfin : eLpNorm f (ENNReal.ofReal p) vol01 < ⊤ :=
      lt_of_le_of_lt ((eLpNorm_le_besovNorm (ENNReal.ofReal p) (1 / p) q f).trans hbes)
        ENNReal.ofReal_lt_top
    have hlq : lqNorm q (besovSeq (ENNReal.ofReal p) (1 / p) f) < ⊤ :=
      lt_of_le_of_lt ((lqNorm_le_besovNorm (ENNReal.ofReal p) (1 / p) q f).trans hbes)
        ENNReal.ofReal_lt_top
    exact (critical_char_radius hp hW hCW hq0 hqt hf hB hbes).mp
      ((mem_besovP_iff _ _ _ f).2 ⟨hfin, hlq⟩)
  · exact FormalizacaoLp.stratum_subset_besov_conn (p := ENNReal.ofReal p)
      (ENNReal.one_le_ofReal.mpr (by linarith)) _ hGm (1 / p) q hq0 hf hs

end FormalizacaoCrit4
