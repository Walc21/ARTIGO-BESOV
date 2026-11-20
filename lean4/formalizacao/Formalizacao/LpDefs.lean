import Mathlib
import Pendencias.Realizacao
import Pendencias.Inversa
import Pendencias.Direta

/-!
# Definições em `L^p` (M0 do plano de formalização)

Espelha, em `ENNReal` e sobre `K = [0,1]`, as definições da Parte IV
(`Pendencias.Agenda`, `Pendencias.Jackson`, `Pendencias.Realizacao`), trocando a
norma uniforme pela norma `L^p`, como no rascunho `conjecturas_lp.tex`
(§ «Definições e notação», equações `lp:eq:second-difference`–`lp:eq:stratum-p`).

A biblioteca `Σ_N = Sigma H N` e as agendas `H_{s,κ}`, `H̃_{s,η}` são as da Parte IV.
Nada aqui é demonstrado: as conjecturas e a hipótese `J_p` são apenas enunciadas.
-/

open MeasureTheory Set ENNReal

namespace FormalizacaoLp

/-- Medida de Lebesgue restrita a `[0,1]` (`K = [0,1]`, `L = 1`). -/
noncomputable abbrev vol01 : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

/-- Segunda diferença `Δ²_h f(x) = f(x+2h) - 2 f(x+h) + f(x)`. -/
def diff2 (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x + 2 * h) - 2 * f (x + h) + f x

/-- `ω_p(f, t) = sup_{0 < h ≤ min{t, 1/2}} ‖Δ²_h f‖_{L^p([0, 1-2h])}`
(eq. `lp:eq:modulus-p`). -/
noncomputable def wtP (p : ℝ≥0∞) (t : ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (h : ℝ) (_ : h ∈ Ioc 0 (min t (1 / 2))),
    eLpNorm (diff2 h f) p (volume.restrict (Icc 0 (1 - 2 * h)))

/-- Distância `‖f - g‖_{L^p([0,1])}` (norma usada no funcional de realização). -/
noncomputable def distP (p : ℝ≥0∞) (f g : ℝ → ℝ) : ℝ≥0∞ :=
  eLpNorm (f - g) p vol01

/-- Funcional de realização em `L^p` (eq. `lp:eq:realization-p`):
`R_N^G(f)_p = inf_{g ∈ G_N} {‖f - g‖_{L^p} + ω_p(g, 1/N)}`. -/
noncomputable def realP (p : ℝ≥0∞) (G : ℕ → Set (ℝ → ℝ)) (N : ℕ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ g ∈ G N, distP p f g + wtP p (1 / (N : ℝ)) g

/-- Norma `ℓ^q` de uma sequência de `ENNReal` (`q = ∞` é o supremo). -/
noncomputable def lqNorm (q : ℝ≥0∞) (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  if q = ⊤ then ⨆ r, a r else (∑' r, a r ^ q.toReal) ^ (q.toReal⁻¹)

/-- Estrato reversível em `L^p` (eq. `lp:eq:stratum-p`):
`R^s_q(G)_p = {f ∈ L^p : ‖(2^{rs} R_{2^r}(f))_{r≥1}‖_{ℓ^q} < ∞}`. Reindexado por `r ↦ r+1`,
como em `Pendencias.Jackson.RGQ`. -/
noncomputable def stratumP (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) (G : ℕ → Set (ℝ → ℝ)) :
    Set (ℝ → ℝ) :=
  {f | eLpNorm f p vol01 < ⊤ ∧ lqNorm q (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s)) *
      realP p G (2 ^ (r + 1)) f) < ⊤}

/-- Espaço de Besov `B^s_{p,q}([0,1])` (eq. `lp:eq:besov-p`):
`f ∈ L^p` e `‖(2^{rs} ω_p(f, 2^{-r}))_{r≥0}‖_{ℓ^q} < ∞`. -/
noncomputable def besovP (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) : Set (ℝ → ℝ) :=
  {f | eLpNorm f p vol01 < ⊤ ∧
    lqNorm q (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) *
      wtP p (1 / (2 : ℝ) ^ r) f) < ⊤}

/-- `A_{N,H}([0,1])`: representações admissíveis com no máximo `N` folhas e altura `≤ H`
(`Pendencias.Agenda.Sigma` sem o ponto `0`). -/
def classNH (N H : ℕ) : Set (ℝ → ℝ) :=
  {g | ∃ T : Artigo.LTree, Artigo.AdmNH N H T ∧ g = T.eval 0 0}

/-! ## Enunciados (não demonstrados) -/

/-- **Conjectura 1, caso `q = ∞`** (`lp:eq:conj-endpoint`): para `f` mensurável,
`f ∈ B^s_{p,∞}` se e só se `f ∈ R^s_∞(Σ, H_{s,0})`, para `1/p < s < 2`. -/
def Conj1Endpoint (p : ℝ≥0∞) (s : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Measurable f →
    (f ∈ besovP p s ⊤ ↔ f ∈ stratumP p s ⊤ (Pendencias.Agenda.Sigma (Pendencias.Agenda.Hsk s 0)))

/-- **Conjectura 1, caso `0 < q < ∞`, `1/p < s < 1`** (`lp:eq:conj-subcritical`). -/
def Conj1Subcritical (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) : Prop :=
  ∀ f : ℝ → ℝ, Measurable f →
    (f ∈ besovP p s q ↔ f ∈ stratumP p s q (Pendencias.Agenda.Sigma (Pendencias.Agenda.Hsk s 0)))

/-- **Conjectura 1, caso `0 < q < ∞`, `1 ≤ s < 2`, `κ > 1/q`** (`lp:eq:conj-critical`). -/
def Conj1Critical (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) (κ : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Measurable f →
    (f ∈ besovP p s q ↔ f ∈ stratumP p s q (Pendencias.Agenda.Sigma (Pendencias.Agenda.Hsk s κ)))

/-- **Conjectura 2 (estabilidade por inclusão de redes)** (`lp:conj:stability`), para a agenda
`H` e a constante `c ≥ 1`: para toda família `𝒩` aninhada, contendo `0`, de funções
mensuráveis, que contém a biblioteca (`Σ^H_N ⊆ 𝒩_{⌈cN⌉}`, eqs. `lp:eq:nesting` e
`lp:eq:contains`), a igualdade `B^s_{p,q} = R^s_q(𝒩)` vale para funções mensuráveis. -/
def Conj2Stability (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) (H : ℕ → ℕ) (c : ℝ) : Prop :=
  1 ≤ c →
  ∀ 𝒩 : ℕ → Set (ℝ → ℝ),
    (∀ N, (0 : ℝ → ℝ) ∈ 𝒩 N) →
    (∀ N, 𝒩 N ⊆ 𝒩 (N + 1)) →
    (∀ N, ∀ g ∈ 𝒩 N, Measurable g) →
    (∀ N, Pendencias.Agenda.Sigma H N ⊆ 𝒩 ⌈c * N⌉₊) →
    ∀ f : ℝ → ℝ, Measurable f → (f ∈ besovP p s q ↔ f ∈ stratumP p s q 𝒩)

/-- **Estabilidade por inclusão aproximada** (`lp:thm:approx-stability`), para a agenda `H`,
constante `c ≥ 1` e sequência de tolerâncias `ε : ℕ → ℝ≥0∞`: se `𝒩` é aninhada, contém `0`,
tem elementos mensuráveis, aproxima `Σ^H_N` em `𝒩_{⌈cN⌉}` com erro em `L^p` no máximo `ε N`,
e `(2^{r s} ε (2^r))_{r≥1} ∈ ℓ^q`, então `B^s_{p,q} = R^s_q(𝒩)`. -/
def Conj2ApproxStability (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) (H : ℕ → ℕ) (c : ℝ)
    (ε : ℕ → ℝ≥0∞) : Prop :=
  1 ≤ c →
  lqNorm q (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s)) *
    ε (2 ^ (r + 1))) < ⊤ →
  ∀ 𝒩 : ℕ → Set (ℝ → ℝ),
    (∀ N, (0 : ℝ → ℝ) ∈ 𝒩 N) →
    (∀ N, 𝒩 N ⊆ 𝒩 (N + 1)) →
    (∀ N, ∀ g ∈ 𝒩 N, Measurable g) →
    (∀ N, ∀ g ∈ Pendencias.Agenda.Sigma H N, ∃ g' ∈ 𝒩 ⌈c * N⌉₊,
      eLpNorm (g - g') p vol01 ≤ ε N) →
    ∀ f : ℝ → ℝ, Measurable f → (f ∈ besovP p s q ↔ f ∈ stratumP p s q 𝒩)

/-- **Hipótese `J_p`** (Jackson racional em `L^p` com altura controlada,
`lp:hyp:jackson`). Para `f` mensurável em `B^s_{p,∞}`, com `R = ‖f‖_∞` (norma uniforme em
`[0,1]`), existem constantes reais `C₀, C₁ ≥ 0` e `n₀` tais que, para toda potência de dois
`n = 2^r ≥ n₀` e todo `H` com `H ≥ max{8 n^{max 1 s}, 32 (R+1)}`, existe `g ∈ A_{n,H}` com
`‖f - g‖_p ≤ C₀ ω_p(f, 1/n) + C₁ (R+1)/H`. -/
def HypJp (p : ℝ≥0∞) (s : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Measurable f → f ∈ besovP p s ⊤ →
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∃ n0 : ℕ,
      ∀ r : ℕ, 2 ^ r ≥ n0 → ∀ H : ℕ,
        (H : ℝ) ≥ max (8 * ((2 : ℝ) ^ r) ^ (max 1 s))
          (32 * ((⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|).toReal + 1)) →
        ∃ g ∈ classNH (2 ^ r) H,
          eLpNorm (f - g) p vol01 ≤
            ENNReal.ofReal C0 * wtP p (1 / (2 : ℝ) ^ r) f +
              ENNReal.ofReal C1 * ENNReal.ofReal ((⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|).toReal + 1)
                / (H : ℝ≥0∞)

end FormalizacaoLp
