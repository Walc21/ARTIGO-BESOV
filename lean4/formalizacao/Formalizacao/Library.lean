import Formalizacao.LpDefs

/-!
# Mensurabilidade da biblioteca `Σ_N` e inclusão `A_{N,H} ⊆ Σ_N`

Os elementos de `Σ_N = Pendencias.Agenda.Sigma H N` são `0` ou `T.eval 0 0` para uma árvore
`T`. Não precisamos da continuidade (que não está formalizada na Parte IV): basta a
mensurabilidade, que segue por indução na árvore, porque `eval` é definido por casos
`if x < c then … else …` sobre folhas afins.
-/

open MeasureTheory Set

namespace FormalizacaoLp

/-- Toda avaliação de árvore é mensurável (indução na árvore). -/
theorem measurable_eval (T : Artigo.LTree) :
    ∀ (k : ℕ) (m : ℤ), Measurable (T.eval k m) := by
  induction T with
  | leaf a =>
    intro k m
    show Measurable (fun x : ℝ => a.eval x)
    unfold Artigo.Atom.eval
    fun_prop
  | node l r ihl ihr =>
    intro k m
    show Measurable (fun x : ℝ =>
      if x < Artigo.cL (k + 1) (2 * m + 1) then l.eval (k + 1) (2 * m) x
      else r.eval (k + 1) (2 * m + 1) x)
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
      (ihl (k + 1) (2 * m)) (ihr (k + 1) (2 * m + 1))

/-- Os elementos de `Σ_N` são mensuráveis. -/
theorem measurable_sigma {H : ℕ → ℕ} {N : ℕ} {g : ℝ → ℝ}
    (hg : g ∈ Pendencias.Agenda.Sigma H N) : Measurable g := by
  simp only [Pendencias.Agenda.Sigma, Set.mem_setOf_eq] at hg
  rcases hg with rfl | ⟨T, -, rfl⟩
  · exact measurable_const
  · exact measurable_eval T 0 0

/-- `A_{N,H(N)} ⊆ Σ_N^H`, pela definição de `Σ`. -/
theorem classNH_subset_sigma (H : ℕ → ℕ) (N : ℕ) :
    classNH N (H N) ⊆ Pendencias.Agenda.Sigma H N := by
  rintro g ⟨T, hT, rfl⟩
  simp only [Pendencias.Agenda.Sigma, Set.mem_setOf_eq]
  exact Or.inr ⟨T, hT, rfl⟩

end FormalizacaoLp
