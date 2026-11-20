import Formalizacao.ModuloENN
import Formalizacao.LpAxioms

/-!
# Conexão: a versão `L^p` como instância da estrutura abstrata

Toma-se `X` = subgrupo aditivo `MeasSub` das funções mensuráveis `ℝ → ℝ`, com a norma
`nrm f = ‖f‖_{L^p([0,1])}` e `ω = wtP p`. Os três axiomas de `ModuloE` são exatamente
`wtP_add_le`, `wtP_le_four` e `wtP_mono_t` (de `Formalizacao.LpAxioms`), e assim
`modC` é uma instância de `ModuloE`.

Para funções mensuráveis `f`, as definições abstratas (`realE`, `stratumE`, `besovE`)
coincidem com as concretas (`realP`, `stratumP`, `besovP` de `Formalizacao.LpDefs`),
e a desigualdade inversa abstrata reproduz `wtP_le_four_realP`.
-/

open MeasureTheory Set ENNReal

namespace FormalizacaoLp

/-- Subgrupo aditivo de `ℝ → ℝ` formado pelas funções mensuráveis. -/
def MeasSub : AddSubgroup (ℝ → ℝ) where
  carrier := {f | Measurable f}
  add_mem' := fun {f g} hf hg => hf.add hg
  zero_mem' := measurable_const
  neg_mem' := fun {f} hf => hf.neg

/-- Norma `L^p([0,1])` nos elementos de `MeasSub`. -/
noncomputable def nrmC (p : ℝ≥0∞) : MeasSub → ℝ≥0∞ :=
  fun f => eLpNorm (f : ℝ → ℝ) p vol01

/-- Instância de `ModuloE`: `ω = wtP p`, `nrm = ‖·‖_{L^p}`. -/
noncomputable def modC {p : ℝ≥0∞} (hp : 1 ≤ p) : Formalizacao.ModE.ModuloE (nrmC p) where
  ω := fun f t => wtP p t (f : ℝ → ℝ)
  subadd := fun f g t => wtP_add_le hp t f.2 g.2
  bound := fun g t => wtP_le_four hp t g.2
  mono := fun f _ _ h => wtP_mono_t p (f : ℝ → ℝ) h

/-- Famílias de funções mensuráveis: `G' N` são os elementos de `MeasSub` em `G N`. -/
def Gc (G : ℕ → Set (ℝ → ℝ)) (N : ℕ) : Set MeasSub := {g | (g : ℝ → ℝ) ∈ G N}

/-- Para funções mensuráveis, o funcional abstrato é o concreto. -/
theorem realE_conn {p : ℝ≥0∞} (hp : 1 ≤ p) (G : ℕ → Set (ℝ → ℝ))
    (hGm : ∀ N, ∀ g ∈ G N, Measurable g) (N : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    Formalizacao.ModE.realE (modC hp) (Gc G) N (⟨f, hf⟩ : MeasSub) = realP p G N f := by
  unfold Formalizacao.ModE.realE realP
  apply le_antisymm
  · exact le_iInf₂ fun g hg => iInf₂_le (⟨g, hGm N g hg⟩ : MeasSub) hg
  · exact le_iInf₂ fun g' hg' => iInf₂_le ((g' : MeasSub) : ℝ → ℝ) hg'

/-- Estrato abstrato = estrato concreto, para funções mensuráveis. -/
theorem stratum_conn {p : ℝ≥0∞} (hp : 1 ≤ p) (G : ℕ → Set (ℝ → ℝ))
    (hGm : ∀ N, ∀ g ∈ G N, Measurable g) (s : ℝ) (q : ℝ≥0∞)
    {f : ℝ → ℝ} (hf : Measurable f) :
    (⟨f, hf⟩ : MeasSub) ∈ Formalizacao.ModE.stratumE (modC hp) (Gc G) s q ↔
      f ∈ stratumP p s q G := by
  have hfun : (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s)) *
      Formalizacao.ModE.realE (modC hp) (Gc G) (2 ^ (r + 1)) (⟨f, hf⟩ : MeasSub)) =
      (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s)) *
        realP p G (2 ^ (r + 1)) f) := by
    funext r
    rw [realE_conn hp G hGm _ hf]
  show (eLpNorm f p vol01 < ⊤ ∧ Formalizacao.ModE.lqE q _ < ⊤) ↔
      (eLpNorm f p vol01 < ⊤ ∧ lqNorm q _ < ⊤)
  rw [hfun]
  rfl

/-- Espaço de Besov abstrato = concreto, para funções mensuráveis. -/
theorem besov_conn {p : ℝ≥0∞} (hp : 1 ≤ p) (s : ℝ) (q : ℝ≥0∞)
    {f : ℝ → ℝ} (hf : Measurable f) :
    (⟨f, hf⟩ : MeasSub) ∈ Formalizacao.ModE.besovE (modC hp) s q ↔ f ∈ besovP p s q :=
  Iff.rfl

/-- A desigualdade inversa abstrata, aplicada à instância `L^p`, dá a versão concreta. -/
theorem wtP_le_four_realP_of_abstract {p : ℝ≥0∞} (hp : 1 ≤ p) (G : ℕ → Set (ℝ → ℝ))
    (hGm : ∀ N, ∀ g ∈ G N, Measurable g) (N : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    wtP p (1 / (N : ℝ)) f ≤ 4 * realP p G N f := by
  have h := Formalizacao.ModE.inverse_E (modC hp) (Gc G) N (⟨f, hf⟩ : MeasSub)
  rw [realE_conn hp G hGm N hf] at h
  exact h

/-- Corolário de inclusão em `L^p` (`R^s_q(G)_p ⊆ B^s_{p,q}`), transferido da versão abstrata,
para funções mensuráveis e `0 < q`. -/
theorem stratum_subset_besov_conn {p : ℝ≥0∞} (hp : 1 ≤ p) (G : ℕ → Set (ℝ → ℝ))
    (hGm : ∀ N, ∀ g ∈ G N, Measurable g) (s : ℝ) (q : ℝ≥0∞) (hq : 0 < q)
    {f : ℝ → ℝ} (hf : Measurable f) (hs : f ∈ stratumP p s q G) :
    f ∈ besovP p s q :=
  (besov_conn hp s q hf).1
    (Formalizacao.ModE.stratum_subset_besovE (modC hp) (Gc G) s q hq
      ((stratum_conn hp G hGm s q hf).2 hs))

end FormalizacaoLp
