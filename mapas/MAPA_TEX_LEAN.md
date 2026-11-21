# Correspondência do artigo sobre $L^p$ com Lean 4

Gerado por `mapas/gerar_mapa.py` a partir de `mapas/dados/mapa_lp.json`. O verificador confere os rótulos do TeX, localiza as declarações nos arquivos indicados e valida os nomes com `#check`. O apêndice A descreve a relação entre os enunciados do artigo e a formalização.

O projeto usa Lean 4.28.0 e Mathlib v4.28.0. A auditoria de dependências axiomáticas está em `lean4/formalizacao/Formalizacao/Auditoria.lean`, com saída registrada em `lean4/formalizacao/auditoria_axiomas.txt`.

Os identificadores preservam o inventário histórico. Os rótulos e as linhas remetem à edição atual. Uma declaração indicada como apoio parcial cobre uma dependência da prova analítica.

## Correspondências

### D1 — módulo de suavidade $\omega_p$ e convenção

Texto: [conjecturas_lp.tex:76](../conjecturas_lp.tex); rótulo `lp:eq:modulus-p`.

Estado: **Formalizado (definição)**. Convenção da Parte IV: a segunda diferença usa $x, x+h, x+2h \in [0,1]$ e o supremo é sobre $0<h\le\min\{t,1/2\}$. A norma é `eLpNorm` na medida de Lebesgue restrita a `[0, 1-2h]`.

- [`FormalizacaoLp.diff2`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 26.
- [`FormalizacaoLp.wtP`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 30.
- [`FormalizacaoLp.vol01`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 23.

### D2 — espaço de Besov diádico $B^s_{p,q}$

Texto: [conjecturas_lp.tex:88](../conjecturas_lp.tex); rótulo `lp:eq:besov-p`.

Estado: **Formalizado (definição)**. `besovP p s q` exige `f ∈ L^p` e a sequência `(2^{rs} ω_p(f, 2^{-r}))_{r≥0}` em `ℓ^q`; a norma `ℓ^q` é `lqNorm` (`q = ∞` é o supremo).

- [`FormalizacaoLp.lqNorm`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 44.
- [`FormalizacaoLp.besovP`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 57.

### D3 — biblioteca $\Sigma_N$ e agendas $H_{s,\kappa}$, $\widetilde H_{s,\eta}$

Texto: [conjecturas_lp.tex:125](../conjecturas_lp.tex); rótulo `lp:eq:schedule`.

Estado: **Formalizado (definição)**. A biblioteca da Parte IV é representada por `Sigma H N = {0} ∪ 𝒜_{N,H(N)}`. As agendas são `Hsk s κ` e `HtilK 0 0 s η`, com `CK 0 0 = 8`. A classe `classNH N H` representa 𝒜_{N,H}.

- [`Pendencias.Agenda.Sigma`](../lean4/formalizacao/Pendencias/Agenda.lean) — linha 24.
- [`Pendencias.Agenda.Hsk`](../lean4/formalizacao/Pendencias/Inversa.lean) — linha 455.
- [`Pendencias.Jackson.HtilK`](../lean4/formalizacao/Pendencias/Direta.lean) — linha 292.
- [`Artigo.AdmNH`](../lean4/formalizacao/RequestProject/JointBudget.lean) — linha 27.
- [`Artigo.LTree`](../lean4/formalizacao/RequestProject/Trees.lean) — linha 61.
- [`FormalizacaoLp.classNH`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 64.

### D4 — mensurabilidade dos elementos de $\Sigma_N$

Texto: [conjecturas_lp.tex:119](../conjecturas_lp.tex); rótulo `lp:eq:sigma`.

Estado: **Formalizado e compilado**. A avaliação de uma árvore é mensurável por indução, pois a avaliação é definida por casos sobre folhas afins.

- [`FormalizacaoLp.measurable_eval`](../lean4/formalizacao/Formalizacao/Library.lean) — linha 17.
- [`FormalizacaoLp.measurable_sigma`](../lean4/formalizacao/Formalizacao/Library.lean) — linha 34.
- [`FormalizacaoLp.classNH_subset_sigma`](../lean4/formalizacao/Formalizacao/Library.lean) — linha 42.

### 2.1 — funcional e espaço de realização em $L^p$

Texto: [conjecturas_lp.tex:142](../conjecturas_lp.tex); rótulo `lp:def:realization`.

Estado: **Formalizado (definição)**. Em `ℝ≥0∞`. O estrato inclui a condição `f ∈ L^p`, como na definição do texto, e é reindexado por `r ↦ r+1` (começa em `N = 2`).

- [`FormalizacaoLp.distP`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 35.
- [`FormalizacaoLp.realP`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 40.
- [`FormalizacaoLp.stratumP`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 50.

### 2.2 — famílias aninhadas que contêm a biblioteca

Texto: [conjecturas_lp.tex:166](../conjecturas_lp.tex); rótulo `lp:def:network-family`.

Estado: **Formalizado (definição)**. As hipóteses de `Conj2Stability` expressam aninhamento, inclusão da função nula e inclusão da biblioteca após reescalonamento do orçamento. A declaração se aplica a famílias mensuráveis, entre elas as famílias de funções contínuas do artigo.

- [`FormalizacaoLp.Conj2Stability`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 89.
- [`FormalizacaoStab.fam_mono`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 26.

### 3.1 — caracterização de Besov por realização aritmética

Texto: [conjecturas_lp.tex:974](../conjecturas_lp.tex); rótulo `lp:conj:besov`.

Estado: **Formalizado e compilado**. Os itens (i), (ii) e (iii) estão formalizados. `conj1_low` e `conj1_diag` usam `p` real com `ENNReal.ofReal p`; as agendas são `Hsk (1 + 1/p - s) 0` e `Hsk 1 (thetaQ q + κ)`, que coincidem com $\widehat H_s$ e $\widehat H_{q,\kappa}$ do texto. O Lean não exige $s>0$ em (ii).

- [`FormalizacaoLp.Conj1Endpoint`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 71.
- [`FormalizacaoLp.Conj1Subcritical`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 76.
- [`FormalizacaoLp.Conj1Critical`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 81.
- [`FormalizacaoJ.conj1_endpoint`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 28.
- [`FormalizacaoJ.conj1_subcritical`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 33.
- [`FormalizacaoJ.conj1_critical`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 39.
- [`FormalizacaoJ.conj1_tilde`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 46.
- [`FormalizacaoLow.conj1_low`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 91.
- [`FormalizacaoLow.conj1_diag`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 102.

### 3.2 — estabilidade por inclusão de redes

Texto: [conjecturas_lp.tex:1007](../conjecturas_lp.tex); rótulo `lp:conj:stability`.

Estado: **Formalizado e compilado**. As quatro declarações `FormalizacaoJ.conj2_*` dão a estabilidade por inclusão para as agendas e os regimes do item (i) do Teorema 3.1 ($1/p<s<2$), com constante real $c\ge1$. `conj2_low` cobre $s<1/p$ e `conj2_diag` cobre $s=1/p$.

- [`FormalizacaoLp.Conj2Stability`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 89.
- [`FormalizacaoJ.conj2_endpoint`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 54.
- [`FormalizacaoJ.conj2_subcritical`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 59.
- [`FormalizacaoJ.conj2_critical`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 65.
- [`FormalizacaoJ.conj2_tilde`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 72.
- [`FormalizacaoLow.conj2_low`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 44.
- [`FormalizacaoLow.conj2_diag`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 69.

### 3.3 — estabilidade por inclusão aproximada

Texto: [conjecturas_lp.tex:1016](../conjecturas_lp.tex); rótulo `lp:thm:approx-stability`.

Estado: **Formalizado e compilado**. A tolerância é `ε : ℕ → ℝ≥0∞`; a somabilidade $(2^{rs}\varepsilon_{2^r})\in\ell^q$ é premissa de `Conj2ApproxStability`. Cobre todos os regimes: $s>1/p$ em `LpJackson3.lean` e $s\le1/p$ em `LowTheorems.lean`.

- [`FormalizacaoLp.Conj2ApproxStability`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 102.
- [`FormalizacaoJ.conj2_approx_endpoint`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 78.
- [`FormalizacaoJ.conj2_approx_subcritical`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 83.
- [`FormalizacaoJ.conj2_approx_critical`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 89.
- [`FormalizacaoJ.conj2_approx_tilde`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 96.
- [`FormalizacaoLow.conj2_approx_low`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 115.
- [`FormalizacaoLow.conj2_approx_diag`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 129.

### 4.1 — estimativa de Jackson em $L^p$

Texto: [conjecturas_lp.tex:190](../conjecturas_lp.tex); rótulo `lp:hyp:jackson`.

Estado: **Formalizado e compilado**. `hypJpStrong_of_lt` dá a estimativa com $C_0=9C_W(p)$ e $C_1=16$ para o representante contínuo. A forma usada nas reduções é demonstrada em `hypJp_of_lt` e permite constantes dependentes de $f$.

- [`FormalizacaoLp.HypJp`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 120.
- [`FormalizacaoJ.hypJp_of_lt`](../lean4/formalizacao/Formalizacao/LpJackson2.lean) — linha 152.
- [`FormalizacaoJ.hypJpStrong_of_lt`](../lean4/formalizacao/Formalizacao/LpJackson4.lean) — linha 30.
- [`FormalizacaoJ.lp_jackson_core`](../lean4/formalizacao/Formalizacao/LpJackson2.lean) — linha 25.

### 4.2 — projeção afim local

Texto: [conjecturas_lp.tex:215](../conjecturas_lp.tex); rótulo `lp:lem:projection`.

Estado: **Formalizado e compilado**. O núcleo reproduz funções afins, é simétrico e tem imagem afim. Os núcleos avaliam a projeção nos extremos, com cotas dadas por Hölder e pela integral do módulo de cada núcleo.

- [`FormalizacaoQuasi.abs_kL_le`](../lean4/formalizacao/Formalizacao/QuasiLocal.lean) — linha 33.
- [`FormalizacaoQuasi.abs_kR_le`](../lean4/formalizacao/Formalizacao/QuasiLocal.lean) — linha 45.
- [`FormalizacaoQuasi.integral_kL_mul_affine`](../lean4/formalizacao/Formalizacao/QuasiLocal.lean) — linha 58.
- [`FormalizacaoQuasi.integral_kR_mul_affine`](../lean4/formalizacao/Formalizacao/QuasiLocal.lean) — linha 98.
- [`FormalizacaoQuasi.abs_integral_kernel_le`](../lean4/formalizacao/Formalizacao/QuasiLocal.lean) — linha 138.
- [`FormalizacaoKer.kernel_is_affine_projection`](../lean4/formalizacao/Formalizacao/Kernel.lean) — linha 111.
- [`FormalizacaoKer.kL_eq_Kf`](../lean4/formalizacao/Formalizacao/Kernel.lean) — linha 27.
- [`FormalizacaoKer.kR_eq_Kf`](../lean4/formalizacao/Formalizacao/Kernel.lean) — linha 33.

### 4.3 — quase-interpolante

Texto: [conjecturas_lp.tex:237](../conjecturas_lp.tex); rótulo `lp:lem:quasi`.

Estado: **Formalizado e compilado**. Construção de $Q_n$, reprodução de funções afins, erro local e cotas de amplitude e de diferenças nodais.

- [`FormalizacaoGrid.Q_affine`](../lean4/formalizacao/Formalizacao/QuasiGrid.lean) — linha 183.
- [`FormalizacaoGrid.Q_cell`](../lean4/formalizacao/Formalizacao/QuasiGrid.lean) — linha 166.
- [`FormalizacaoGrid.abs_lam_sup_le`](../lean4/formalizacao/Formalizacao/QuasiGrid.lean) — linha 244.
- [`FormalizacaoGrid.local_error`](../lean4/formalizacao/Formalizacao/LocalError.lean) — linha 177.
- [`FormalizacaoL52d.lam_diff_le`](../lean4/formalizacao/Formalizacao/Lemma52d.lean) — linha 83.
- [`FormalizacaoL52d.omega1`](../lean4/formalizacao/Formalizacao/Lemma52d.lean) — linha 24.

### 4.4 — Whitney em partições de $L^p$

Texto: [conjecturas_lp.tex:264](../conjecturas_lp.tex); rótulo `lp:lem:whitney`.

Estado: **Formalizado e compilado**. A prova usa média dupla, fórmula de Taylor, reflexão, Jensen e Tonelli. A transferência das duas faixas extremas para o interior e a multiplicidade dos intervalos dão a estimativa global.

- [`FormalizacaoW.whitney_lp`](../lean4/formalizacao/Formalizacao/Whitney12.lean) — linha 31.
- [`FormalizacaoW.local_whitney`](../lean4/formalizacao/Formalizacao/Whitney7.lean) — linha 62.
- [`FormalizacaoW.taylor_lp`](../lean4/formalizacao/Formalizacao/Whitney2.lean) — linha 17.
- [`FormalizacaoW.double_sym`](../lean4/formalizacao/Formalizacao/Whitney3.lean) — linha 73.
- [`FormalizacaoW.fg_lp`](../lean4/formalizacao/Formalizacao/Whitney4.lean) — linha 140.
- [`FormalizacaoW.sum_lintegral_le`](../lean4/formalizacao/Formalizacao/Whitney8.lean) — linha 64.
- [`FormalizacaoW.Wt_global`](../lean4/formalizacao/Formalizacao/Whitney9.lean) — linha 15.
- [`FormalizacaoW.Ek_bound`](../lean4/formalizacao/Formalizacao/Whitney10.lean) — linha 77.
- [`FormalizacaoCor.WhitneyLp`](../lean4/formalizacao/Formalizacao/Corollary54.lean) — linha 32.

### 4.5 — erro de quase-interpolação

Texto: [conjecturas_lp.tex:330](../conjecturas_lp.tex); rótulo `lp:cor:quasi-error`.

Estado: **Formalizado e compilado**. `quasi_error_unc` deduz a cota global de `whitney_lp` e do erro local.

- [`FormalizacaoCor.quasi_error`](../lean4/formalizacao/Formalizacao/Corollary54.lean) — linha 124.
- [`FormalizacaoCor.local_error_inf`](../lean4/formalizacao/Formalizacao/Corollary54.lean) — linha 97.
- [`FormalizacaoCor.sum_cells_le`](../lean4/formalizacao/Formalizacao/Corollary54.lean) — linha 109.
- [`FormalizacaoW.quasi_error_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 18.

### 4.6 — imersão e cota de $\omega_1$

Texto: [conjecturas_lp.tex:345](../conjecturas_lp.tex); rótulo `lp:lem:embedding`.

Estado: **Formalizado e compilado**. A cota de Besov controla a série telescópica das diferenças de quase-interpolantes. A série fornece o representante contínuo e as estimativas do módulo de primeira ordem.

- [`FormalizacaoEmb.inverse_affine_sup`](../lean4/formalizacao/Formalizacao/Embedding.lean) — linha 90.
- [`FormalizacaoEmb.bernstein_affine`](../lean4/formalizacao/Formalizacao/Embedding.lean) — linha 100.
- [`FormalizacaoL55b.vk_sup_le`](../lean4/formalizacao/Formalizacao/Lemma55b.lean) — linha 108.
- [`FormalizacaoL55b.vk_slope_le`](../lean4/formalizacao/Formalizacao/Lemma55b.lean) — linha 159.
- [`FormalizacaoL55c.ae_eq_Glim`](../lean4/formalizacao/Formalizacao/Lemma55c.lean) — linha 284.
- [`FormalizacaoL55c.Glim_continuousOn`](../lean4/formalizacao/Formalizacao/Lemma55c.lean) — linha 215.
- [`FormalizacaoL55d.F_lip`](../lean4/formalizacao/Formalizacao/Lemma55d.lean) — linha 141.
- [`FormalizacaoL55e.modulus_lt1`](../lean4/formalizacao/Formalizacao/Lemma55e.lean) — linha 187.
- [`FormalizacaoL55e.modulus_eq1`](../lean4/formalizacao/Formalizacao/Lemma55e.lean) — linha 267.
- [`FormalizacaoL55e.modulus_gt1`](../lean4/formalizacao/Formalizacao/Lemma55e.lean) — linha 322.
- [`FormalizacaoW.Glim_continuousOn_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 27.
- [`FormalizacaoW.ae_eq_Glim_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 37.
- [`FormalizacaoW.modulus_lt1_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 47.
- [`FormalizacaoW.modulus_eq1_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 59.
- [`FormalizacaoW.modulus_gt1_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 72.
- [`FormalizacaoJ.besov_continuous_rep`](../lean4/formalizacao/Formalizacao/LpJackson4.lean) — linha 87.

### 4.7 — interpolação racional com orçamento de altura

Texto: [conjecturas_lp.tex:387](../conjecturas_lp.tex); rótulo `lp:prop:jackson-proof`.

Estado: **Formalizado e compilado**. `nodal_tree` constrói o interpolante quantizado sob cotas de altura e de inclinação. A estimativa `lp_jackson_core` aplica essa construção aos valores nodais de $Q_n f$.

- [`FormalizacaoJ.nodal_tree`](../lean4/formalizacao/Formalizacao/LpJackson0.lean) — linha 18.
- [`FormalizacaoJ.Q_node`](../lean4/formalizacao/Formalizacao/LpJackson1.lean) — linha 16.
- [`FormalizacaoJ.lam_congr_ae`](../lean4/formalizacao/Formalizacao/LpJackson1.lean) — linha 38.
- [`FormalizacaoJ.nodal_G`](../lean4/formalizacao/Formalizacao/LpJackson1.lean) — linha 55.
- [`FormalizacaoJ.hypJp_of_lt`](../lean4/formalizacao/Formalizacao/LpJackson2.lean) — linha 152.

### 4.8 — interpolação racional sem controle dos saltos

Texto: [conjecturas_lp.tex:472](../conjecturas_lp.tex); rótulo `lp:lem:nodal-general`.

Estado: **Formalizado e compilado**. Árvore nodal com `Q = 2^e ≥ 2^r` e `H ≥ 8(M+1)Q`, sem hipótese sobre `|y_{n+1}-y_n|`; `lp_jackson_low_core` é o núcleo do Jackson para $s\le1/p$.

- [`FormalizacaoJ.nodal_tree_gen`](../lean4/formalizacao/Formalizacao/LowNodal.lean) — linha 19.
- [`FormalizacaoJ.lp_jackson_low_core`](../lean4/formalizacao/Formalizacao/LowJackson.lean) — linha 18.

### 4.9 — cota em sup dos quase-interpolantes

Texto: [conjecturas_lp.tex:481](../conjecturas_lp.tex); rótulo `lp:lem:sup-bound`.

Estado: **Formalizado e compilado**. Na forma «existe `K ≥ 1`, dependendo de `f`», com `Lam p s q r` $=\Lambda_r$. As somas parciais de $\ell^q$ estão em `sum_le_lq`.

- [`FormalizacaoLow.step_le`](../lean4/formalizacao/Formalizacao/LowSup.lean) — linha 33.
- [`FormalizacaoLow.Q_sup_le`](../lean4/formalizacao/Formalizacao/LowSup.lean) — linha 61.
- [`FormalizacaoLow.Lam`](../lean4/formalizacao/Formalizacao/LowSup.lean) — linha 89.
- [`FormalizacaoLow.lam_bound`](../lean4/formalizacao/Formalizacao/LowSup.lean) — linha 114.
- [`FormalizacaoLow.thetaQ`](../lean4/formalizacao/Formalizacao/LowSum.lean) — linha 19.
- [`FormalizacaoLow.sum_le_lq`](../lean4/formalizacao/Formalizacao/LowSum.lean) — linha 53.

### 4.10 — Jackson para $s\le1/p$

Texto: [conjecturas_lp.tex:505](../conjecturas_lp.tex); rótulo `lp:thm:jackson-low`.

Estado: **Formalizado e compilado**. As constantes $C_W$ e $K$ dependem de `f`, em vez de $C_0(S+1)$ do texto.

- [`FormalizacaoLow.classNH_le_sigma`](../lean4/formalizacao/Formalizacao/LowJackson2.lean) — linha 19.
- [`FormalizacaoLow.jackson_low`](../lean4/formalizacao/Formalizacao/LowJackson2.lean) — linha 24.

### 5.1 — propriedades do módulo em $L^p$

Texto: [conjecturas_lp.tex:93](../conjecturas_lp.tex); rótulo `lp:lem:modulus`.

Estado: **Formalizado e compilado**. Para `1 ≤ p` e funções mensuráveis. `modC` mostra que são exatamente os três axiomas do arcabouço abstrato.

- [`FormalizacaoLp.wtP_add_le`](../lean4/formalizacao/Formalizacao/LpAxioms.lean) — linha 42.
- [`FormalizacaoLp.wtP_le_four`](../lean4/formalizacao/Formalizacao/LpAxioms.lean) — linha 152.
- [`FormalizacaoLp.wtP_mono_t`](../lean4/formalizacao/Formalizacao/LpAxioms.lean) — linha 53.
- [`FormalizacaoLp.modC`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 33.
- [`Formalizacao.ModE.ModuloE`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 21.

### 5.2 — desigualdade inversa em $L^p$

Texto: [conjecturas_lp.tex:1039](../conjecturas_lp.tex); rótulo `lp:prop:inverse`.

Estado: **Formalizado e compilado**. A cota `ω_p(f,1/N) ≤ 4 R_N(f)` vale para toda família de funções mensuráveis; a segunda afirmação usa `0 ∈ G_N`. Também está provada no arcabouço abstrato, em valores reais e em `ℝ≥0∞`, e transferida à instância `L^p`.

- [`FormalizacaoLp.wtP_le_four_realP`](../lean4/formalizacao/Formalizacao/LpAxioms.lean) — linha 162.
- [`FormalizacaoRed.realP_le_norm`](../lean4/formalizacao/Formalizacao/Reductions.lean) — linha 113.
- [`Formalizacao.ModE.inverse_E`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 52.
- [`Formalizacao.inverse_le`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 59.
- [`FormalizacaoLp.wtP_le_four_realP_of_abstract`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 75.

### 5.3 — inclusão $\mathscr R\subset B$

Texto: [conjecturas_lp.tex:1059](../conjecturas_lp.tex); rótulo `lp:cor:inclusion`.

Estado: **Formalizado e compilado**. Vale para `0 < q ≤ ∞`, qualquer família de funções mensuráveis, sem relação com a agenda.

- [`FormalizacaoLp.stratum_subset_besov_conn`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 84.
- [`Formalizacao.ModE.stratum_subset_besovE`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 109.
- [`Formalizacao.ModE.lqE_lt_top_of_succ_le`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 70.
- [`Formalizacao.stratum_subset_besov`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 139.

### 5.4 — critério de somabilidade da agenda

Texto: [conjecturas_lp.tex:1071](../conjecturas_lp.tex); rótulo `lp:thm:besov-conditional`.

Estado: **Formalizado e compilado, condicional a $J_p$**. `besov_subset_stratum` usa a estimativa de Jackson para a inclusão direta sob o critério de somabilidade. As quatro reduções especializam a agenda.

- [`FormalizacaoRed.besov_subset_stratum`](../lean4/formalizacao/Formalizacao/Reductions.lean) — linha 137.
- [`FormalizacaoRed.realP_le_of_approx`](../lean4/formalizacao/Formalizacao/Reductions.lean) — linha 41.
- [`FormalizacaoThm.conj1_endpoint_of_J`](../lean4/formalizacao/Formalizacao/Theorems.lean) — linha 27.
- [`FormalizacaoThm.conj1_subcritical_of_J`](../lean4/formalizacao/Formalizacao/Theorems.lean) — linha 44.
- [`FormalizacaoThm.conj1_critical_of_J`](../lean4/formalizacao/Formalizacao/Theorems.lean) — linha 71.
- [`FormalizacaoThm.conj1_tilde_of_J`](../lean4/formalizacao/Formalizacao/Theorems.lean) — linha 90.
- [`FormalizacaoSched.weight_bdd`](../lean4/formalizacao/Formalizacao/Schedules.lean) — linha 163.
- [`FormalizacaoSched.weight_geom`](../lean4/formalizacao/Formalizacao/Schedules.lean) — linha 45.
- [`FormalizacaoSched.weight_poly`](../lean4/formalizacao/Formalizacao/Schedules.lean) — linha 79.
- [`FormalizacaoSched.Hsk_low`](../lean4/formalizacao/Formalizacao/Schedules.lean) — linha 132.
- [`FormalizacaoSched.Htil_low`](../lean4/formalizacao/Formalizacao/Schedules.lean) — linha 151.
- [`FormalizacaoLq.lq_of_eventually_le`](../lean4/formalizacao/Formalizacao/LqLemmas.lean) — linha 128.
- [`FormalizacaoLq.lq_of_geom_le`](../lean4/formalizacao/Formalizacao/LqLemmas.lean) — linha 168.
- [`FormalizacaoLq.lq_of_poly_le`](../lean4/formalizacao/Formalizacao/LqLemmas.lean) — linha 200.

### 5.5 — transferência da estimativa direta para famílias aninhadas

Texto: [conjecturas_lp.tex:1106](../conjecturas_lp.tex); rótulo `lp:thm:stability-conditional`.

Estado: **Formalizado e compilado, condicional a $J_p$**. O aproximante de Jackson na escala deslocada fornece a inclusão direta. A desigualdade inversa dá a igualdade nas declarações de estabilidade.

- [`FormalizacaoStab.besov_subset_stratum_fam`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 183.
- [`FormalizacaoStab.stability_iff_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 226.
- [`FormalizacaoStab.conj2Stability_endpoint_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 339.
- [`FormalizacaoStab.conj2Stability_subcritical_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 343.
- [`FormalizacaoStab.conj2Stability_critical_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 349.
- [`FormalizacaoStab.conj2Stability_tilde_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 356.
- [`FormalizacaoRed.realP_le_of_approx'`](../lean4/formalizacao/Formalizacao/Reductions.lean) — linha 86.
- [`FormalizacaoLq.lq_tail_le`](../lean4/formalizacao/Formalizacao/LqLemmas.lean) — linha 233.

### 5.6 — transferência sob inclusão aproximada para $s>1/p$

Texto: [conjecturas_lp.tex:1127](../conjecturas_lp.tex); rótulo `lp:thm:approx-transfer`.

Estado: **Formalizado e compilado, condicional a $J_p$**. O núcleo com tolerância é `besov_subset_stratum_fam_core`; o teorema sem tolerância é o caso $\varepsilon=0$.

- [`FormalizacaoStab.besov_subset_stratum_fam_approx`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 203.
- [`FormalizacaoStab.stability_approx_iff_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 365.
- [`FormalizacaoStab.conj2ApproxStability_endpoint_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 384.
- [`FormalizacaoStab.conj2ApproxStability_subcritical_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 397.
- [`FormalizacaoStab.conj2ApproxStability_critical_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 420.
- [`FormalizacaoStab.conj2ApproxStability_tilde_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 436.

### 5.7 — transferência para $s\le1/p$

Texto: [conjecturas_lp.tex:1150](../conjecturas_lp.tex); rótulo `lp:thm:low-transfer`.

Estado: **Formalizado e compilado**. A condição de deslocamento do texto é `hshift`; o expoente extra `m` é `0` ($s<1/p$) ou `mDiag κ` ($s=1/p$).

- [`FormalizacaoLow.besov_subset_stratum_low`](../lean4/formalizacao/Formalizacao/LowTransfer.lean) — linha 178.
- [`FormalizacaoLow.hshift_low`](../lean4/formalizacao/Formalizacao/LowShift.lean) — linha 21.
- [`FormalizacaoLow.hshift_diag`](../lean4/formalizacao/Formalizacao/LowShift.lean) — linha 75.
- [`FormalizacaoLow.mDiag`](../lean4/formalizacao/Formalizacao/LowWeights.lean) — linha 65.
- [`FormalizacaoLow.mDiag_ge`](../lean4/formalizacao/Formalizacao/LowWeights.lean) — linha 72.
- [`FormalizacaoLow.mDiag_le`](../lean4/formalizacao/Formalizacao/LowWeights.lean) — linha 78.
- [`FormalizacaoLow.wreal_geom`](../lean4/formalizacao/Formalizacao/LowWeights.lean) — linha 45.
- [`FormalizacaoLow.wreal_poly`](../lean4/formalizacao/Formalizacao/LowWeights.lean) — linha 90.
- [`FormalizacaoLow.hW_geom`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 23.
- [`FormalizacaoLow.hW_poly`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 34.
- [`FormalizacaoLow.sigma_family`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 80.

### 5.8 — transferência aproximada para $s\le1/p$

Texto: [conjecturas_lp.tex:1184](../conjecturas_lp.tex); rótulo `lp:thm:low-approx-transfer`.

Estado: **Formalizado e compilado**. `besov_subset_stratum_low` é o caso $\varepsilon=0$ do núcleo com tolerância.

- [`FormalizacaoLow.besov_subset_stratum_low_core`](../lean4/formalizacao/Formalizacao/LowTransfer.lean) — linha 21.
- [`FormalizacaoLow.besov_subset_stratum_low_approx`](../lean4/formalizacao/Formalizacao/LowTransfer.lean) — linha 200.
- [`FormalizacaoLow.hW_diag`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 56.

### 6.1 — dados de regime e agenda uniforme

Texto: [conjecturas_lp.tex:529](../conjecturas_lp.tex); rótulo `lp:def:regime`.

Estado: **Formalizado (definição)**. A norma da bola é a soma da norma em $L^p$ e da norma da sequência de Besov. Os expoentes, o fator de crescimento e a condição de admissibilidade distinguem os três regimes.

- [`FormalizacaoLow.besovNorm`](../lean4/formalizacao/Formalizacao/UnifSup.lean) — linha 23.
- [`FormalizacaoLow.LamU`](../lean4/formalizacao/Formalizacao/UnifSup.lean) — linha 27.
- [`FormalizacaoLow.nuPrime`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 36.
- [`FormalizacaoLow.kapPrime`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 38.
- [`FormalizacaoLow.nuHat`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 40.
- [`FormalizacaoLow.kapHat`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 43.
- [`FormalizacaoLow.Hunif`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 47.
- [`FormalizacaoLow.UniformAdmissible`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 182.

### 6.2 — altura e quantização uniformes

Texto: [conjecturas_lp.tex:554](../conjecturas_lp.tex); rótulo `lp:lem:uniform-height`.

Estado: **Formalizado e compilado**. A potência de dois é mínima. A cota nodal tem constante comum à bola. O peso de quantização inclui o fator $1/2$ do erro nodal.

- [`FormalizacaoLow.qexp_le_of_target_le`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 186.
- [`FormalizacaoLow.uniform_height_quantization`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 205.
- [`FormalizacaoLow.uniform_quantWeight_lt_top`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 221.
- [`FormalizacaoLow.lam_bound_unif`](../lean4/formalizacao/Formalizacao/UnifSup.lean) — linha 138.

### 6.3 — cotas uniformes sobre bolas

Texto: [conjecturas_lp.tex:572](../conjecturas_lp.tex); rótulo `lp:thm:uniform`.

Estado: **Formalizado e compilado**. As constantes de altura e de Whitney são escolhidas antes de $\kappa$, do raio e da função. A cota pontual vale para toda escala diádica $n\ge2$. A cota em $\ell^q$ requer admissibilidade.

- [`FormalizacaoLow.uniform_besov_ball`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 409.

### 6.4 — peso sem o fator logarítmico

Texto: [conjecturas_lp.tex:600](../conjecturas_lp.tex); rótulo `lp:obs:uniform-q`.

Estado: **Formalizado e compilado**. A taxa pontual admite $\kappa=0$. Com $s\ge1$ e $q$ finito, o peso de quantização com $\kappa=0$ é limitado e afastado de zero, logo a série diverge.

- [`FormalizacaoLow.uniform_besov_ball`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 409.
- [`FormalizacaoRegular.uniform_quantWeight_zero_not_lt_top`](../lean4/formalizacao/Formalizacao/RegularSchedules.lean) — linha 161.

### 6.5 — piso aritmético em $L^p$

Texto: [conjecturas_lp.tex:673](../conjecturas_lp.tex); rótulo `lp:prop:floor`.

Estado: **Formalizado e compilado**. A distância racional é exata. A integral em cada folha dá a cota em $L^1$, que se estende a $L^p$ pela monotonia da norma na medida de probabilidade de $[0,1]$.

- [`FormalizacaoFloor.rational_arithmetic_floor`](../lean4/formalizacao/Formalizacao/ArithmeticFloor.lean) — linha 35.
- [`FormalizacaoFloor.arithmetic_floor_lp`](../lean4/formalizacao/Formalizacao/ArithmeticFloor.lean) — linha 129.
- [`FormalizacaoFloor.arithmetic_floor_bestError`](../lean4/formalizacao/Formalizacao/ArithmeticFloor.lean) — linha 148.

### 6.6–6.7 — necessidade da altura para a taxa uniforme

Texto: [conjecturas_lp.tex:693](../conjecturas_lp.tex); rótulo `lp:cor:floor`.

Estado: **Formalizado e compilado**. A função constante de teste pertence à bola unitária. O corolário usa $0<s<2$ e $N\ge2$. A declaração de necessidade em Lean admite $N\ge1$ para qualquer $s\in\mathbb R$. A cota de realização em `uniform_besov_ball` com $\kappa=0$ fornece a direção suficiente da observação quando $1\le s<2$, $s>1/p$ e $B\ge1$.

- [`FormalizacaoFloor.arithmetic_height_necessary`](../lean4/formalizacao/Formalizacao/ArithmeticFloor.lean) — linha 168.
- [`FormalizacaoLow.uniform_besov_ball`](../lean4/formalizacao/Formalizacao/UnifTheorem.lean) — linha 409.

### 6.8 — código binário de comprimento limitado

Texto: [conjecturas_lp.tex:1334](../conjecturas_lp.tex); rótulo `lp:prop:bits`.

Estado: **Formalizado e compilado**. O orçamento é compartilhado. O código contém um bit inicial, a forma em pré-ordem e as coordenadas de cada folha em largura fixa. A contagem usa a ausência de prefixos próprios e obtém $\log_2\#\Sigma_N\le4N(c_H+1)$.

- [`FormalizacaoBits.coordinateWidth_eq`](../lean4/formalizacao/Formalizacao/BinaryBudget.lean) — linha 18.
- [`FormalizacaoBits.treeWord_prefix`](../lean4/formalizacao/Formalizacao/BinaryBudget.lean) — linha 148.
- [`FormalizacaoBits.boundedLibrary_code`](../lean4/formalizacao/Formalizacao/BinaryBudget.lean) — linha 178.
- [`FormalizacaoBits.boundedLibrary_card`](../lean4/formalizacao/Formalizacao/BinaryBudget.lean) — linha 209.
- [`FormalizacaoBits.boundedLibrary_log_card`](../lean4/formalizacao/Formalizacao/BinaryBudget.lean) — linha 231.

### 6.9 — taxa e bits sobre bolas

Texto: [conjecturas_lp.tex:1343](../conjecturas_lp.tex); rótulo `lp:cor:bits`.

Estado: **Formalizado e compilado**. O mesmo aproximante satisfaz a cota de erro e a cota de comprimento, com constantes que só dependem dos índices.

- [`FormalizacaoBits.uniform_rate_bits`](../lean4/formalizacao/Formalizacao/BinaryBudget.lean) — linha 314.

### 6.11 — critério exato para agendas regulares

Texto: [conjecturas_lp.tex:1264](../conjecturas_lp.tex); rótulo `lp:prop:regular`.

Estado: **Formalizado e compilado**. As duas equivalências usam comparabilidade com o fator recíproco e condensação de Cauchy. As séries começam em um por reindexação.

- [`FormalizacaoRegular.Hregular`](../lean4/formalizacao/Formalizacao/RegularSchedules.lean) — linha 16.
- [`FormalizacaoRegular.regular_schedule_criterion`](../lean4/formalizacao/Formalizacao/RegularSchedules.lean) — linha 124.

### 6.12 — caracterização, estabilidade e cotas uniformes com log-log

Texto: [conjecturas_lp.tex:1278](../conjecturas_lp.tex); rótulo `lp:cor:loglog`.

Estado: **Formalizado e compilado**. O critério da agenda vale exatamente quando $\gamma q>1$. O corolário usa as reduções de Jackson já demonstradas, incluindo estabilidade por inclusão aproximada.

- [`FormalizacaoLogLog.HlogLog`](../lean4/formalizacao/Formalizacao/LogLogSchedules.lean) — linha 58.
- [`FormalizacaoLogLog.logLog_schedule_iff`](../lean4/formalizacao/Formalizacao/LogLogSchedules.lean) — linha 61.
- [`FormalizacaoLogLog.conj1_loglog`](../lean4/formalizacao/Formalizacao/LogLogSchedules.lean) — linha 79.
- [`FormalizacaoLogLog.conj2_loglog`](../lean4/formalizacao/Formalizacao/LogLogSchedules.lean) — linha 90.
- [`FormalizacaoLogLog.conj2_approx_loglog`](../lean4/formalizacao/Formalizacao/LogLogSchedules.lean) — linha 100.
- [`FormalizacaoLogLog.uniform_loglog_ball`](../lean4/formalizacao/Formalizacao/LogLogSchedules.lean) — linha 162.

### 6.13 — comparação de agendas, séries de Bertrand e diagonal

Texto: [conjecturas_lp.tex:1295](../conjecturas_lp.tex); rótulo `lp:obs:loglog`.

Estado: **Formalizado e compilado**. A razão para a agenda de log simples tende a zero. A série diverge no limiar crítico e o critério vale para qualquer número positivo de logaritmos. Na diagonal $p=s=1$ a agenda contém o fator adicional $L_1^{\theta_q}$.

- [`FormalizacaoLogLog.logLog_schedule_ratio_tendsto_zero`](../lean4/formalizacao/Formalizacao/LogLogSchedules.lean) — linha 324.
- [`FormalizacaoLogLog.logLog_schedule_iff`](../lean4/formalizacao/Formalizacao/LogLogSchedules.lean) — linha 61.
- [`FormalizacaoLogLog.HlogLogDiag_eq`](../lean4/formalizacao/Formalizacao/LogLogSchedules.lean) — linha 201.
- [`FormalizacaoLogLog.conj1_loglog_diagonal`](../lean4/formalizacao/Formalizacao/LogLogSchedules.lean) — linha 292.
- [`FormalizacaoIterated.bertrand_summable_iff`](../lean4/formalizacao/Formalizacao/IteratedSchedules.lean) — linha 89.
- [`FormalizacaoIterated.iterated_schedule_iff`](../lean4/formalizacao/Formalizacao/IteratedSchedules.lean) — linha 188.

### F1 — arcabouço abstrato do módulo, em valores reais

Texto: [conjecturas_lp.tex:1415](../conjecturas_lp.tex); rótulo `lp:sec:lean`.

Estado: **Formalizado e compilado**. Estrutura `ModuloAbs` sobre um espaço seminormado; `ω` real. Serve de modelo para a versão em `ℝ≥0∞`, usada na instância `L^p`.

- [`Formalizacao.ModuloAbs`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 22.
- [`Formalizacao.ModuloAbs.realization`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 41.
- [`Formalizacao.ModuloAbs.stratum`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 46.
- [`Formalizacao.ModuloAbs.besov`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 50.
- [`Formalizacao.memℓp_of_succ_le`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 102.

### F2 — arcabouço abstrato em $\mathbb R_{\ge0}^\infty$ e sua instância $L^p$

Texto: [conjecturas_lp.tex:1415](../conjecturas_lp.tex); rótulo `lp:sec:lean`.

Estado: **Formalizado e compilado**. A instância usa o subgrupo `MeasSub` das funções mensuráveis, com `nrm = eLpNorm · p vol01` e `ω = wtP p`. Os teoremas de conexão mostram que `realE`, `stratumE` e `besovE` coincidem com `realP`, `stratumP` e `besovP` para funções mensuráveis.

- [`Formalizacao.ModE.realE`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 38.
- [`Formalizacao.ModE.stratumE`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 42.
- [`Formalizacao.ModE.besovE`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 47.
- [`FormalizacaoLp.MeasSub`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 22.
- [`FormalizacaoLp.realE_conn`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 43.
- [`FormalizacaoLp.stratum_conn`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 52.
- [`FormalizacaoLp.besov_conn`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 69.

### F3 — Jackson racional com altura explícita sobre dados nodais (Parte IV, Lema IV.4.1)

Texto: [conjecturas_lp.tex:1415](../conjecturas_lp.tex); rótulo `lp:sec:lean`.

Estado: **Formalizado e compilado**. O núcleo `jackson_nodal` aceita dados nodais $y_j$ com erro nodal controlado. A forma para dados pontuais recupera a estimativa de Jackson da Parte IV.

- [`Pendencias.Jackson.jackson_nodal`](../lean4/formalizacao/Pendencias/Jackson.lean) — linha 447.
- [`Pendencias.Jackson.atom_height_nodal`](../lean4/formalizacao/Pendencias/Jackson.lean) — linha 334.
- [`Pendencias.Jackson.rational_jackson_height`](../lean4/formalizacao/Pendencias/Jackson.lean) — linha 512.
- [`Pendencias.Jackson.rational_jackson_uniform_explicit`](../lean4/formalizacao/Pendencias/Jackson.lean) — linha 599.

### F4 — Arcabouço abstrato instanciado em $L^\infty$ (Parte IV)

Texto: [conjecturas_lp.tex:1415](../conjecturas_lp.tex); rótulo `lp:sec:lean`.

Estado: **Formalizado e compilado**. O segundo módulo e a norma uniforme da Parte IV satisfazem os três axiomas; a desigualdade inversa e a inclusão $\mathscr R\subset B$ em $L^\infty$ são reobtidas dos teoremas abstratos.

- [`FormalizacaoInf.modInf`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 45.
- [`FormalizacaoInf.realE_modInf`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 51.
- [`FormalizacaoInf.inverse_realG_of_abstract`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 58.
- [`FormalizacaoInf.besovE_top_iff`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 74.
- [`FormalizacaoInf.besovE_fin_iff`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 90.
- [`FormalizacaoInf.besovQ_of_RGQ_abstract`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 117.
- [`FormalizacaoInf.besovInf_of_RGInf_abstract`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 131.

### A1 — quantização com salto limitado $J$ (Parte V, Lema 4.7 estendido)

Texto: [conjecturas_lp.tex:425](../conjecturas_lp.tex); rótulo `lp:lem:nodal-jump`.

Estado: **Formalizado e compilado**. `quantization_jump` separa os casos $n\le Q$ e $n>Q$. No segundo, `nodal_tree_coarse` usa paridades alternadas para garantir inclinações inteiras não nulas e controla a altura pelo salto nodal.

- [`FormalizacaoAltura.quantization_jump`](../lean4/formalizacao/Formalizacao/AlturaQuant.lean) — linha 21.
- [`FormalizacaoJ.nodal_tree_gen`](../lean4/formalizacao/Formalizacao/LowNodal.lean) — linha 19.; caso n ≤ Q.
- [`FormalizacaoJ.nodal_tree_coarse`](../lean4/formalizacao/Formalizacao/AlturaCoarse.lean) — linha 18.; caso n > Q.

### A2 — saltos nodais uniformes do quase-interpolante

Texto: [conjecturas_lp.tex:607](../conjecturas_lp.tex); rótulo `lp:lem:critical-jump`.

Estado: **Apoio Lean (salto com hipóteses por célula)**. A soma telescópica aceita a cota de sup em Q₂ e as cotas de inclinação em cada nível como hipóteses, sem parâmetro p. A aplicação a p=1 com o controle analítico do módulo é explicitada no texto.

- [`FormalizacaoCrit.nodal_jump`](../lean4/formalizacao/Formalizacao/AlturaCritical.lean) — linha 82.

### A3 — altura linear crítica para $s=1/p$, $p>1$

Texto: [conjecturas_lp.tex:622](../conjecturas_lp.tex); rótulo `lp:thm:critical-linear`.

Estado: **Formalizado para q finito, extensão analítica a q infinito**. A agenda crítica usa a constante `Avc p CW`, independente de q, e o fator B+1. As declarações por nível usam controle de cada coeficiente do módulo, sem introduzir q. As estimativas em sequência e a inclusão direta na bola exigem `q ≠ ⊤` no Lean. O texto também prova o caso q infinito.

- [`FormalizacaoCrit.critical_approx`](../lean4/formalizacao/Formalizacao/AlturaCritical.lean) — linha 266.; quantização de $Q_nf$ no item (a), combinada no texto com o erro de quase-interpolação.
- [`FormalizacaoCrit2.critical_level`](../lean4/formalizacao/Formalizacao/AlturaCritical2.lean) — linha 135.; cota de realização por nível.
- [`FormalizacaoCrit3.critical_lq`](../lean4/formalizacao/Formalizacao/AlturaCritical3.lean) — linha 311.; item (c).
- [`FormalizacaoCrit3.critical_rate`](../lean4/formalizacao/Formalizacao/AlturaCritical3.lean) — linha 514.; item (b).
- [`FormalizacaoCrit3.critical_char_radius`](../lean4/formalizacao/Formalizacao/AlturaCritical3.lean) — linha 556.; item (d).
- [`FormalizacaoCrit4.critical_radius_ball_and_inclusion`](../lean4/formalizacao/Formalizacao/AlturaRadius.lean) — linha 20.; item (d): bola ⊆ Rstr e Rstr ⊆ B.

### A4 — piso geométrico em toda a biblioteca

Texto: [conjecturas_lp.tex:747](../conjecturas_lp.tex); rótulo `lp:prop:geom-floor`.

Estado: **Formalizado e compilado**. Teste suave com última folha, distância positiva a afins por integração por partes, e cota de Besov do bump escalado. O campo do endereço da última folha implica m+1=2^k≤H, com a consequência formal em `terminal_affine`.

- [`FormalizacaoAltura.geometric_floor`](../lean4/formalizacao/Formalizacao/AlturaFloor.lean) — linha 363.
- [`FormalizacaoAltura.geometric_dist_lower`](../lean4/formalizacao/Formalizacao/AlturaFloor.lean) — linha 309.
- [`FormalizacaoAltura.L1_affine_lower`](../lean4/formalizacao/Formalizacao/AlturaFloor.lean) — linha 144.
- [`FormalizacaoAltura.terminal_affine`](../lean4/formalizacao/Formalizacao/AlturaTerminal.lean) — linha 192.
- [`FormalizacaoAltura.classNH_lipschitz`](../lean4/formalizacao/Formalizacao/AlturaTerminal.lean) — linha 221.
- [`FormalizacaoAltura.besovNorm_bumpS_le`](../lean4/formalizacao/Formalizacao/AlturaBesov.lean) — linha 252.

### A5 — piso por inclinação em toda a biblioteca

Texto: [conjecturas_lp.tex:763](../conjecturas_lp.tex); rótulo `lp:prop:slope-floor`.

Estado: **Formalizado e compilado**. Dois intervalos disjuntos, convexidade em $\ell^p$ e Lipschitz da biblioteca com constante $H$.

- [`FormalizacaoAltura.slope_floor`](../lean4/formalizacao/Formalizacao/AlturaSlope.lean) — linha 250.
- [`FormalizacaoAltura.two_interval_pointwise`](../lean4/formalizacao/Formalizacao/AlturaSlope.lean) — linha 23.
- [`FormalizacaoAltura.slope_dist_lower`](../lean4/formalizacao/Formalizacao/AlturaSlope.lean) — linha 158.

### A6 — necessidade conjunta (erro e realização)

Texto: [conjecturas_lp.tex:781](../conjecturas_lp.tex); rótulo `lp:cor:joint-necessity`.

Estado: **Formalizado e compilado**. No texto, o melhor erro vale para $N\ge1$ e a variante com realização para $N\ge2$. As versões com realização em `AlturaTransfer.lean` usam o funcional estendido de Lean, em que $N\ge1$ é admissível.

- [`FormalizacaoAltura.geometric_necessity`](../lean4/formalizacao/Formalizacao/AlturaNecessity.lean) — linha 85.
- [`FormalizacaoAltura.slope_necessity`](../lean4/formalizacao/Formalizacao/AlturaNecessity.lean) — linha 108.
- [`FormalizacaoAltura.arithmetic_necessity`](../lean4/formalizacao/Formalizacao/AlturaNecessity.lean) — linha 136.
- [`FormalizacaoAltura.geometric_necessity_realP`](../lean4/formalizacao/Formalizacao/AlturaTransfer.lean) — linha 67.
- [`FormalizacaoAltura.slope_necessity_realP`](../lean4/formalizacao/Formalizacao/AlturaTransfer.lean) — linha 81.
- [`FormalizacaoAltura.arithmetic_necessity_realP`](../lean4/formalizacao/Formalizacao/AlturaTransfer.lean) — linha 95.

### A7 — transferência exata entre erro e realização

Texto: [conjecturas_lp.tex:924](../conjecturas_lp.tex); rótulo `lp:prop:transfer`.

Estado: **Formalizado e compilado**. As duas desigualdades são provadas em Lean com valores em $[0,+\infty]$. A proposição do manuscrito as usa para $N\ge2$, $f\in L^p$ e $G_N\subseteq L^p$, com $+\infty$ para os ínfimos da família vazia.

- [`FormalizacaoAltura.bestError_le_realP`](../lean4/formalizacao/Formalizacao/AlturaTransfer.lean) — linha 22.
- [`FormalizacaoAltura.realP_le_bestError_add`](../lean4/formalizacao/Formalizacao/AlturaTransfer.lean) — linha 55.

### A8 — escopo da altura crítica (dependência de $B$, $q$ e agenda única)

Texto: [conjecturas_lp.tex:1248](../conjecturas_lp.tex); rótulo `lp:obs:critical-scope`.

Estado: **Observação (escopo)**. Distingue a agenda calibrada pelo raio, a agenda linear fixa e o endpoint p=s=1. A caracterização global sob a agenda fixa, inclusive no endpoint por supremo, é analítica.

### A9 — fecho da comparação de potências (Observação)

Texto: [conjecturas_lp.tex:953](../conjecturas_lp.tex); rótulo `lp:obs:floor-closure`.

Estado: **Observação**. O minimax por escala dá a potência ótima em toda a faixa, inclusive p=s=1. A necessidade é uniforme na bola e pode usar alvos que dependem dos orçamentos.

### A10 — escala de um bump e constante do piso

Texto: [conjecturas_lp.tex:716](../conjecturas_lp.tex); rótulo `lp:lem:bump`.

Estado: **Formalizado e compilado**. Norma de Besov do bump escalado e cota inferior em L^p por integração por partes e Hölder; usado na prova de lp:prop:geom-floor.

- [`FormalizacaoAltura.besovNorm_bumpS_le`](../lean4/formalizacao/Formalizacao/AlturaBesov.lean) — linha 252.; norma de Besov com Λ.
- [`FormalizacaoAltura.geometric_dist_lower`](../lean4/formalizacao/Formalizacao/AlturaFloor.lean) — linha 309.; cota inferior com κ/M.

### E1 — empacotamento de Besov por bumps disjuntos

Texto: [conjecturas_lp.tex:794](../conjecturas_lp.tex); rótulo `lp:lem:packing`.

Estado: **Demonstrado no texto (sem formalização Lean)**. Família $f_\theta$ com norma de Besov $\le B$, separação em $L^p$ por distância de Hamming e empacotamento binário. Sem declaração Lean correspondente.

### E2 — cota inferior de entropia métrica

Texto: [conjecturas_lp.tex:1356](../conjecturas_lp.tex); rótulo `lp:prop:entropy-lower`.

Estado: **Demonstrado no texto (sem formalização Lean)**. Vale para $0<\varepsilon\le\varepsilon_0B$, com centros arbitrários em $L^p$. Não afirma cota superior. Sem declaração Lean correspondente.

### E3 — cota inferior de bits

Texto: [conjecturas_lp.tex:1382](../conjecturas_lp.tex); rótulo `lp:cor:bits-lower`.

Estado: **Demonstrado no texto (sem formalização Lean)**. $L\ge c_5N-1$ para códigos de comprimento máximo $L$ com erro uniforme $C_BN^{-s}$. Sem declaração Lean correspondente.

### E4 — limites da entropia (observação)

Texto: [conjecturas_lp.tex:1398](../conjecturas_lp.tex); rótulo `lp:obs:entropy`.

Estado: **Demonstrado no texto (sem formalização Lean)**. O corte $\varepsilon_0B$ é suficiente para a prova por empacotamento. Para $\varepsilon\ge B$, a cobertura usa uma bola de centro zero. As escalas intermediárias ficam fora do enunciado da cota inferior.

### M1 — constante 4 na desigualdade de Nikolskii

Texto: [conjecturas_lp.tex:365](../conjecturas_lp.tex); rótulo `lp:eq:nikolskii`.

Estado: **Justificação analítica com apoio Lean**. A especialização a funções afins usa P_Iv=v, a estimativa nos extremos e a fórmula elementar da inclinação.

- [`FormalizacaoKer.kernel_is_affine_projection`](../lean4/formalizacao/Formalizacao/Kernel.lean) — linha 111. Apoio parcial para esta prova.
- [`FormalizacaoQuasi.abs_integral_kernel_le`](../lean4/formalizacao/Formalizacao/QuasiLocal.lean) — linha 138. Apoio parcial para esta prova.

### M2 — piso pelo número de folhas

Texto: [conjecturas_lp.tex:865](../conjecturas_lp.tex); rótulo `lp:lem:leaf-budget-floor`.

Estado: **Demonstrado no texto (sem formalização Lean)**. A contagem das células de teste livres de fronteiras e o argumento com 2N bumps são analíticos. O teste de distância a funções afins em uma célula oferece apoio parcial.

- [`FormalizacaoAltura.L1_affine_lower`](../lean4/formalizacao/Formalizacao/AlturaFloor.lean) — linha 144. Apoio parcial para esta prova.

### M3 — quantização com denominador por nó

Texto: [conjecturas_lp.tex:447](../conjecturas_lp.tex); rótulo `lp:lem:nodal-variable-height`.

Estado: **Demonstrado no texto (sem formalização Lean)**. A quantização variável usa um denominador comum por folha e duas exclusões nos nós ímpares. A declaração de denominador comum em toda a malha cobre a construção anterior.

### M4 — altura linear em B¹₁,q por escala

Texto: [conjecturas_lp.tex:649](../conjecturas_lp.tex); rótulo `lp:prop:l1-linear-height`.

Estado: **Demonstrado no texto (sem formalização Lean)**. A média dos módulos dos valores nodais e o novo lema de quantização dão a cota em p=s=1. A declaração citada controla a soma dos saltos sob hipóteses por célula.

- [`FormalizacaoCrit.nodal_jump`](../lean4/formalizacao/Formalizacao/AlturaCritical.lean) — linha 82. Apoio parcial para esta prova.

### M5 — lei minimax conjunta em N e H

Texto: [conjecturas_lp.tex:886](../conjecturas_lp.tex); rótulo `lp:thm:minimax-nh`.

Estado: **Demonstrado no texto (sem formalização Lean)**. A equivalência conjunta combina o piso em folhas com os três pisos de altura e as construções por escala. O enunciado final, com supremo sobre a bola e ambos os orçamentos livres, é analítico.

- [`FormalizacaoAltura.geometric_floor`](../lean4/formalizacao/Formalizacao/AlturaFloor.lean) — linha 363. Apoio parcial para esta prova.
- [`FormalizacaoAltura.slope_floor`](../lean4/formalizacao/Formalizacao/AlturaSlope.lean) — linha 250. Apoio parcial para esta prova.
- [`FormalizacaoFloor.arithmetic_floor_bestError`](../lean4/formalizacao/Formalizacao/ArithmeticFloor.lean) — linha 148. Apoio parcial para esta prova.

### M6 — lei minimax do funcional de realização

Texto: [conjecturas_lp.tex:936](../conjecturas_lp.tex); rótulo `lp:cor:minimax-realization`.

Estado: **Demonstrado no texto (sem formalização Lean)**. A comparação por escala está formalizada. A equivalência minimax, incluindo a redução de todo N ao nível diádico para controlar o módulo, é demonstrada no texto.

- [`FormalizacaoAltura.bestError_le_realP`](../lean4/formalizacao/Formalizacao/AlturaTransfer.lean) — linha 22. Apoio parcial para esta prova.
- [`FormalizacaoAltura.realP_le_bestError_add`](../lean4/formalizacao/Formalizacao/AlturaTransfer.lean) — linha 55. Apoio parcial para esta prova.

### M7 — agenda linear fixa global

Texto: [conjecturas_lp.tex:1211](../conjecturas_lp.tex); rótulo `lp:thm:critical-fixed-agenda`.

Estado: **Demonstrado no texto (sem formalização Lean)**. A agenda fixa usa deslocamento dependente do raio e trata todo 0<q≤∞. A inclusão inversa universal é formalizada.

- [`FormalizacaoLp.stratum_subset_besov_conn`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 84. Apoio parcial para esta prova.

### M8 — crescimento ótimo em função do raio

Texto: [conjecturas_lp.tex:1229](../conjecturas_lp.tex); rótulo `lp:prop:critical-radius-growth`.

Estado: **Demonstrado no texto (sem formalização Lean)**. A cota em função do raio e a obstrução por constantes são analíticas. A estimativa por bola de q finito para a agenda calibrada é um apoio parcial.

- [`FormalizacaoCrit3.critical_lq`](../lean4/formalizacao/Formalizacao/AlturaCritical3.lean) — linha 311. Apoio parcial para esta prova.

## Resumo

| Estado | Entradas |
|---|---|
| Formalizado e compilado | 39 |
| Demonstrado no texto (sem formalização Lean) | 11 |
| Formalizado (definição) | 6 |
| Formalizado e compilado, condicional a $J_p$ | 3 |
| Apoio Lean (salto com hipóteses por célula) | 1 |
| Formalizado para q finito, extensão analítica a q infinito | 1 |
| Observação (escopo) | 1 |
| Observação | 1 |
| Justificação analítica com apoio Lean | 1 |
