# Relatório F1 — Auditoria integral de dependências para a formalização do Teorema 5.2

**Teorema-alvo:** `lp:thm:minimax-nh` (`conjecturas_lp.tex`, linhas 885–892)
**Branch:** `formalizacao-teorema-5-2`
**SHA inicial:** `f02baea6faffd563ddf7877548b59827854dea1e`
**Tag editorial congelada:** `editorial-v1.0` (anotada; aponta para `f02baea`, inalterada)
**Escopo desta etapa:** diagnóstico, grafo de dependências e plano F2–F6. Nenhuma demonstração nova, nenhuma alteração em módulos Lean, no manuscrito, em mapas, scripts, testes, README ou relatórios anteriores.

---

## 1. Resumo executivo

1. **O Teorema 5.2 não está formalizado em Lean.** Não há no código nenhuma declaração que estabeleça `c(N^{-s}+H^{-s/a(p,s)}) ≤ D_{p,s,q}(N,H) ≤ C(N^{-s}+H^{-s/a(p,s)})`. Não existe sequer uma definição Lean de `D_{p,s,q}(N,H)` nem de `a(p,s)` como função explícita. O próprio manuscrito é coerente com isso: o apêndice Lean (`conjecturas_lp.tex`, linhas 1414–1486) lista as declarações verificadas e não inclui `lp:thm:minimax-nh`, e `mapas/AUDITORIA_FIDELIDADE.md:100` registra que "a equivalência minimax conjunta é analítica".
2. **A parte inferior de altura está quase toda formalizada.** Os três pisos de altura do manuscrito têm correspondentes Lean demonstrados e com enunciado fiel: piso geométrico `H^{-s}` (`geometric_floor`), piso por inclinação `H^{-s/(1+1/p-s)}` (`slope_floor`) e piso aritmético `1/(2H)` (`arithmetic_floor_lp`).
3. **A parte inferior em número de folhas, `N^{-s}`, está ausente.** Falta `lp:lem:leaf-budget-floor` e seu lema de empacotamento `lp:lem:packing`. É o maior bloqueio da cota inferior.
4. **A parte superior tem um núcleo uniforme, mas incompleto.** `uniform_besov_ball` (`Formalizacao/UnifTheorem.lean:409`) dá, com constantes independentes de `f` e da bola, um aproximante em `classNH (2^r) (H(2^r))` com erro `≤ C·n^{-s}` para `n=2^r`. Não estão cobertos:
   - a independência de orçamentos `(N,H)` arbitrários (arredondamento para potências de dois);
   - `p=s=1` com `q>1` (altura com fator logarítmico em vez de linear);
   - `s=1/p`, `p>1`, `q=∞` (os teoremas críticos exigem `q≠∞`).
5. **Divergências a tratar:** `HypJp` (`Formalizacao/LpDefs.lean:120`) mede `R` pelo `toReal` de um supremo pontual sobre um representante arbitrário, o que não coincide com `R=‖f‖_∞` do representante contínuo do manuscript; e `JointBudget.lean` mede o erro em **norma uniforme**, não em `L^p`. Nenhum dos dois pode ser usado diretamente como equivalente do Teorema 5.2.
6. **Caminho crítico:** (i) definir `D_{p,s,q}` e `a(p,s)` em Lean; (ii) formalizar `lp:lem:packing` e o piso de folhas; (iii) completar a cota superior nos casos `p=s=1, q>1` e `s=1/p, q=∞`; (iv) formalizar o arredondamento dos orçamentos; (v) compor o teorema com a forma exata do enunciado.
7. **Compilação:** `lake build Formalizacao` concluiu com sucesso (8133 jobs, sem erros). A auditoria de axiomas e a varredura de `sorry` estão na seção 15.
8. **F2 pode começar** sem decisões arquiteturais em aberto (seção 17). As decisões de definição (`D`, `a(p,s)`) são simples e podem ser tomadas no início de F2.

---

## 2. Estado inicial da branch

| Item | Valor observado |
|---|---|
| Repositório remoto (`origin`) | `https://github.com/Walc21/ARTIGO-BESOV.git` (confere com o alvo) |
| Branch ativa | `formalizacao-teorema-5-2` (confere) |
| SHA de `HEAD` no início | `f02baea6faffd563ddf7877548b59827854dea1e` (confere) |
| `git status` no início | árvore limpa; "up to date with origin/formalizacao-teorema-5-2" |
| Tag `editorial-v1.0` | objeto de tag anotada; peel para `f02baea6faffd563ddf7877548b59827854dea1e` (confere) |
| Branch `pesquisa-minimax-altura` | aponta para `f02baea` (não alterada) |
| Branch `main` | aponta para `36192a75fc8c0b4f26e4690c5778357a8aea4874` (não alterada) |
| Operações Git ativas | **Nenhuma.** |

**Sobre o `REBASE_HEAD` residual.** O arquivo `.git/REBASE_HEAD` existe e contém `98a11b9111839606f0ed7f22bc290b743fc15df0` (commit "Revisa o artigo e adiciona edições ABNT e em inglês"). Verificações feitas:

- `.git/rebase-merge` e `.git/rebase-apply` não existem, portanto não há rebase em andamento segundo os mecanismos do Git;
- `git status` não reporta operação em curso;
- `98a11b9` **não é ancestral** de `HEAD` (`git merge-base --is-ancestor` retornou falha), o que indica um arquivo residual de uma operação antiga, sem efeito no estado atual.

O arquivo **não foi removido**, conforme solicitado.

**Ignorados pelo Git (preexistentes, não tocados):** `.lake/` em `lean4/formalizacao` e auxiliares LaTeX (`*.aux`, `*.log`, `*.fls`, `*.fdb_latexmk`).

---

## 3. Enunciado matemático-alvo

Fonte principal: `conjecturas_lp.tex`.

- Definição de `D` (linha 858–860): `D_{p,s,q}(N,H) = sup_{‖f‖*≤1} e^H_{N,p}(f)`, com `e^H_{N,p}(f) = inf_{g∈Σ_{N,H}} ‖f−g‖_p` e `Σ_{N,H} = {0} ∪ 𝒜_{N,H}([0,1])` (`lp:eq:sigma`).
- Enunciado (`lp:thm:minimax-nh`, linhas 886–892): para `1≤p<∞`, `0<s<2`, `0<q≤∞`, existem `c,C>0` dependentes só de `(p,s,q)` tais que, para todos os inteiros `N,H≥2`,
  `c(N^{-s}+H^{-s/a(p,s)}) ≤ D_{p,s,q}(N,H) ≤ C(N^{-s}+H^{-s/a(p,s)})`,
  com `a(p,s) = 1+1/p−s` se `0<s<1/p`; `1` se `1/p≤s≤1`; `s` se `1<s<2`.
- Definição de quase-norma (`lp:eq:besov-p`, seção «Espaços de Besov e biblioteca racional»): `‖f‖*_{B^s_{p,q}} = ‖f‖_p + ‖(2^{rs} ω_p(f,2^{-r}))_{r≥0}‖_{ℓ^q}`, com `q=∞` por supremo.
- Altura (subseção «Altura aritmética e funcional de realização»): `height(a/b)=max{|a|,b}`; altura de segmento `u+v(x−x_{k,m})` igual a `max{2,k+1,|m|+1,height(u),height(v)}`, com `v≠0`.

**Verificação de correspondência do enunciado de F1:** o enunciado acima foi lido diretamente do `.tex` congelado. O enunciado em inglês (`conjecturas_lp_en.tex`) não foi necessário para resolver ambiguidades.

**Observação sobre a faixa de `s` na prova do manuscrito:** a prova (linhas 886–935) cobre `s<1/p`, `1/p<s≤1` (incluindo `p=s=1` e `s=1/p` com `p>1`) e `1<s<2`. Os casos de fronteira são tratados explicitamente no texto, em concordância com o enunciado.

---

## 4. Inventário de definições

Todas as definições abaixo foram lidas nos arquivos indicados. Os números de linha são do estado atual do repositório.

| Definição (qualificada) | Arquivo:linha | Papel | Observação de fidelidade |
|---|---|---|---|
| `Formalizacao.besovNorm` | `Formalizacao/UnifSup.lean:23` | `eLpNorm f p vol01 + lqNorm q (besovSeq p s f)` em `ℝ≥0∞` | Coincide com `‖f‖*` do manuscrito. Usa `vol01` (Lebesgue em `[0,1]`), `q=⊤` via `lqNorm`. |
| `Formalizacao.besovSeq` | `Formalizacao/Reductions.lean:24` | `r ↦ 2^{rs}·wtP p (1/2^r) f`, `r : ℕ` | Índices `r≥0`, como no manuscrito. |
| `FormalizacaoLp.wtP` | `Formalizacao/LpDefs.lean:30` | `sup_{0<h≤min(t,1/2)} ‖Δ²_h f‖_{L^p([0,1−2h])}` | Fiel a `lp:eq:modulus-p` (linhas 70–80). Medida restrita a `[0,1−2h]`. |
| `FormalizacaoLp.besovP` | `Formalizacao/LpDefs.lean:57` | `{f | ‖f‖_p<∞ ∧ lqNorm q(…)<∞}` | Fiel. |
| `FormalizacaoLp.lqNorm` | `Formalizacao/LpDefs.lean:44` | `q=⊤ ↦ sup`; senão `(∑ a_r^q)^{1/q}` | Fiel. |
| `FormalizacaoLp.distP` | `Formalizacao/LpDefs.lean:35` | `eLpNorm (f−g) p vol01` | Fiel (`‖f−g‖_p`). |
| `FormalizacaoLp.realP` | `Formalizacao/LpDefs.lean:40` | `⨅ g∈G N, distP f g + wtP (1/N) g` | Fiel a `lp:eq:realization-p`. `⨅` sobre vazio dá `⊤`, convenção do manuscrito. |
| `FormalizacaoLp.classNH` | `Formalizacao/LpDefs.lean:64` | `{g | ∃T, AdmNH N H T ∧ g = T.eval 0 0}` | Corresponde a `𝒜_{N,H}([0,1])`. |
| `Pendencias.Agenda.Sigma` | `Pendencias/Agenda.lean:24` | `{g | g=0 ∨ ∃T, AdmNH N (H N) T ∧ g = T.eval 0 0}` | Corresponde a `Σ_{N,H}={0}∪𝒜_{N,H}`. **Observação:** o módulo vive em `Pendencias/`, mas é importado pela biblioteca principal (ver §16, R-5). |
| `Artigo.Atom` | `RequestProject/Atoms.lean:17` | `k, m, y0 : ℚ, s : ℚ, hs : s ≠ 0` | Segmento `y0 + s(x−centro)` com `s≠0`, fiel a "v ∈ ℚ∖{0}". |
| `Artigo.Atom.height` | `RequestProject/Atoms.lean:45` | `max(2, k+1, |m|+1, ht y0, ht s)` | Fiel à altura do manuscrito. |
| `Artigo.ht` | `RequestProject/Indexing.lean:129` | `max |num| den` | Fiel a `height(a/b)`. |
| `Artigo.LTree` / `LTree.maxHeight` | `RequestProject/Trees.lean:61, 110` | árvore binária; máximo das alturas das folhas | Fiel. |
| `Artigo.AdmNH` | `RequestProject/JointBudget.lean:27` | `WF 0 0 T ∧ numLeaves ≤ N ∧ maxHeight ≤ H` | Fiel a `N` folhas e altura `≤ H`. |
| `FormalizacaoFloor.bestError` | `Formalizacao/ArithmeticFloor.lean:145` | `⨅ g∈Sigma(fun _ ↦ H) N, distP p f g` | Fiel a `e^H_{N,p}(f)`. |
| `FormalizacaoLow.nuHat` | `Formalizacao/UnifTheorem.lean:40` | `max(1,s)` se `1/p<s`; `1+1/p−s` se `s<1/p`; `1` caso contrário | **Coincide pontualmente com `a(p,s)`** em todas as faixas (verificado caso a caso). Não há, porém, uma definição `aPS` nomeada e a equivalência não está provada como lema. |
| `kapHat` | `Formalizacao/UnifTheorem.lean:43` | `κ` se `1/p<s`; `0` se `s<1/p`; `θ_q+κ` se `s=1/p` | Fator logarítmico. Em `s=1/p` com `q>1` introduz `log`, ver GAP-007/008. |
| `Hunif` | `Formalizacao/UnifTheorem.lean:47` | `⌈A(B+1)(N+1)^ν·L(N)^κ⌉` | Agenda uniforme. |
| `UniformAdmissible` | `Formalizacao/UnifTheorem.lean:182` | `q≠⊤ → 1≤s → 1/q<κ` | Condição apenas para a parte `ℓ^q` de `uniform_besov_ball`; não é necessária para a cota por escala. |
| `FormalizacaoJ.HypJpStrong` | `Formalizacao/LpJackson4.lean:19` | `∃C0,C1, ∀f contínua em B^s_{p,∞}, ∃n0, ∀ r, … ∃g∈classNH(2^r,H), ‖f−g‖_p ≤ C0 ω + C1(R+1)/H` | Fiel a `lp:hyp:jackson`: `C0,C1` antes de `f`, `n0` depois (como no manuscrito, linha 190–199). |
| `FormalizacaoLp.HypJp` | `Formalizacao/LpDefs.lean:120` | como acima, sem continuidade; `C0,C1,n0` depois de `f`; `R=(⨆ x∈[0,1], ofReal|f x|).toReal` | **Divergente** (ver GAP-013): `toReal` de supremo pontual de representante arbitrário, e constantes dependentes de `f`. |
| `criticalAgenda` | `Formalizacao/AlturaCritical3.lean:33` | `⌈Avc p CW (B+1)(N+1)⌉` | Corresponde a `H_B(N)` de `lp:thm:critical-linear`. |
| `supDist` / `jointErr` / `leafErr` | `RequestProject/JointBudget.lean:23, 30, 34` | erro em **norma uniforme** (`⨆ x∈[0,1]`) | **Divergente** para o Teorema 5.2, que é em `L^p` (ver GAP-014). |

**Definições ausentes:** `D_{p,s,q}(N,H)` (sup sobre a bola de Besov), `a(p,s)` como função nomeada, e a Besov-ball `‖f‖*≤1` como conjunto. Ver GAP-001.

---

## 5. Inventário de resultados Lean

Os resultados abaixo foram lidos pelo enunciado. Demonstrações não foram lidas linha a linha para todos os casos; quando a classificação depende de uma leitura parcial, isso é indicado.

**Compilação e cobertura:** `lake build Formalizacao` concluiu com sucesso. A biblioteca tem 76 arquivos em `Formalizacao/`, 54 em `Pendencias/`, 31 em `RequestProject/`, totalizando cerca de 40.600 linhas `.lean` fora de `.lake`.

### 5.1. Teoremas e lemas de cota inferior (altura)

| Declaração | Arquivo:linha | Tipo (resumido) | Hipóteses | Dependências diretas |
|---|---|---|---|---|
| `rational_arithmetic_floor` | `Formalizacao/ArithmeticFloor.lean:35` | `infDist(1/(2H), Q_H) = 1/(2H)` | `1≤H` | `Pendencias.Agenda.QH`, `ht` |
| `arithmetic_floor_lp` | `Formalizacao/ArithmeticFloor.lean:129` | `1/(2H) ≤ distP p (const) g` para `g∈Sigma(H) N`, **todo N** | `1≤p`, `1≤H`, `g∈Sigma` | `leaf_floor`, `vol01_univ` |
| `arithmetic_floor_bestError` | `Formalizacao/ArithmeticFloor.lean:148` | versão com `bestError` | `1≤p`, `1≤H` | `arithmetic_floor_lp` |
| `arithmetic_height_necessary` | `Formalizacao/ArithmeticFloor.lean:168` | `N^s/(2C) ≤ H N` se o erro é `≤ C N^{-s}` | `hrate` | `arithmetic_floor_bestError` |
| `geometric_floor` | `Formalizacao/AlturaFloor.lean:363` | `∃c, ∀H≥2, ∃f, ‖f‖*≤1 ∧ ∀N, ∀g∈Σ_{N,H}, c H^{-s} ≤ ‖f−g‖_p` | `1≤p`, `p≠⊤`, `0<q`, `0<s<2` | `geometric_dist_lower`, `besovNorm_bumpS_le`, `φB` |
| `slope_floor` | `Formalizacao/AlturaSlope.lean:250` | `∃c, ∀H≥2, ∃f, ‖f‖*≤1 ∧ ∀N, ∀g∈Σ_{N,H}, c H^{-s/(1+(1/p−s))} ≤ ‖f−g‖_p` | `1≤p`, `0<q`, `0<s<2`, `s≤1/p` | `two_interval_pointwise`, `slope_dist_lower`, `besovNorm_bumpS_le` |
| `geometric_dist_lower` | `Formalizacao/AlturaFloor.lean:309` | cota inferior de `L^p` para bump com afim em célula | `1≤p`, `M>0` | `lp_lower_of_L1`, `L1_affine_lower` |
| `lp_lower_of_L1` | `Formalizacao/AlturaFloor.lean:261` | `L^1 ⇒ L^p` para funções contínuas | `1≤p`, `p≠⊤` | `eLpNorm_one_interval` |
| `L1_affine_lower` | `Formalizacao/AlturaFloor.lean:144` | piso de `L^1` para afim sobre bump | `M>0` | `kappaB_pos`, integrais de `φB` |
| `besovNorm_bumpS_le` | `Formalizacao/AlturaBesov.lean:252` | `‖bumpS φ a x0 t‖* ≤ Λ|a|t^{1/p−s}` | `0<s<2`, `φ` suave e suportada em `(0,1)` | `wtP_bumpS_le`, `xr_*` |
| `geometric_necessity`, `slope_necessity`, `arithmetic_necessity` | `Formalizacao/AlturaNecessity.lean:85, 108, 136` | cotas de necessidade de altura | hipóteses de taxa | `besovNorm_const_le`, `height_of_rate` |

**Nota:** `geometric_floor` está enunciado para `0<s<2` sem restrição de faixa `1/p≤s≤1`. Isso é uma generalização legítima: a cota `c H^{-s}` é válida para todo `s`, e nas faixas em que o manuscrito a usa (`1/p≤s≤1`) coincide com `H^{-s/a}`. Nas demais faixas, `H^{-s}` é mais fraca do que `H^{-s/a}`, e o teorema usa o piso correto.

### 5.2. Teoremas e lemas de cota superior

| Declaração | Arquivo:linha | Tipo (resumido) | Hipóteses | Constantes |
|---|---|---|---|---|
| `whitney_lp` | `Formalizacao/Whitney12.lean:31` | `∃CW, 0≤CW ∧ WhitneyLp p CW` | `1≤p` | **Incondicional** |
| `quasi_error_unc` | `Formalizacao/Whitney13.lean:18` | erro da quase-interpolação `Q_n`, com `CW` | `1≤p` | `CW(p)` |
| `Q_cell`, `Q_affine` | `Formalizacao/QuasiGrid.lean:166, 183` | `Q_n` reproduz afins em cada célula | `1≤n` | — |
| `besov_continuous_rep` | `Formalizacao/LpJackson4.lean:87` | `f=G` q.t.p. em `[0,1]`, `G` contínua | `1≤p`, `1/p<s`, `f∈B^s_{p,∞}` | — |
| `hypJpStrong_of_lt` | `Formalizacao/LpJackson4.lean:30` | `HypJpStrong (ofReal p) s` | `1≤p`, `1/p<s` | `C0=9C_W(p)`, `C1=16`; **`n0=n0(f)`** |
| `hypJp_of_lt` | `Formalizacao/LpJackson2.lean:152` | `HypJp (ofReal p) s` | `1≤p`, `1/p<s` | **constantes dependentes de `f`** |
| `hypJp_of_lt'` | `Formalizacao/LpJackson3.lean:19` | versão com `p:ℝ≥0∞` | `1≤p`, `p≠⊤` | idem |
| `lp_jackson_core` | `Formalizacao/LpJackson2.lean:25` | núcleo de Jackson com nodal | `1≤p`, quase-interpolação | — |
| `jackson_low` | `Formalizacao/LowJackson2.lean:24` | Jackson para `s≤1/p` | `1≤p`, `s≤1/p`, `f∈B` | **`CW, K` dependem de `f`** (depois de `hbes`) |
| `lp_jackson_low_core` | `Formalizacao/LowJackson.lean:18` | núcleo para `s≤1/p` | — | — |
| `nodal_jump` | `Formalizacao/AlturaCritical.lean:82` | salto nodal por `Q_{2^r}` | `|Q_2 f| ≤ V0` | — |
| `quantization_jump` | `Formalizacao/AlturaQuant.lean:21` | quantização com denominador `2^r` comum; `AdmNH (2^r) H` | `8·2^r ≤ H`, `16(M+1) ≤ H`, `2^r(J+1) ≤ H` | denominador **comum** |
| `nodal_tree_gen` | `Formalizacao/LowNodal.lean:19` | quantização sem controle de saltos | — | — |
| `nodal_tree_coarse` | `Formalizacao/AlturaCoarse.lean:18` | variante grossa | — | — |
| `lam_bound_unif` | `Formalizacao/UnifSup.lean:138` | cota uniforme de `Λ_r` | `1≤p`, `0<q` | — |
| `uniform_height_quantization` | `Formalizacao/UnifTheorem.lean:205` | `Q=2^{qexp}`; `1/Q ≤ 2^{-rs}`; altura `≤ 2^{rν}L^κ` | `1≤p`, `0≤κ`, `1≤r` | denominador **comum** `Q` |
| `uniform_ball_of_budget` | `Formalizacao/UnifTheorem.lean:315` | agenda genérica com `e`, `height` | `1≤p`, `0<q` | `CW, Cs` **antes** de `f`, `B` |
| `uniform_besov_ball` | `Formalizacao/UnifTheorem.lean:409` | por escala: `∃g∈classNH(2^r, H(2^r))`, `dist ≤ (9CW B+1)2^{-rs}`; `ℓ^q` sob `UniformAdmissible` | `1≤p`, `0<q`, `s<2` | `CW, Cs` **antes** de `κ,B,f` |
| `critical_approx` | `Formalizacao/AlturaCritical.lean:266` | aproximação crítica com `H ≥ 16(B0+…)` | `1<p`, `WhitneyLp p CW` | — |
| `critical_level` | `Formalizacao/AlturaCritical2.lean:90` | nível crítico | `1<p`, `WhitneyLp p CW` | — |
| `critical_lq` | `Formalizacao/AlturaCritical3.lean:311` | `ℓ^q` da altura crítica | `1<p`, `q≠⊤` | **exige `q<∞`** |
| `critical_rate` | `Formalizacao/AlturaCritical3.lean:514` | taxa `(B+1) n^{-1/p}` com `criticalAgenda` linear | `1<p`, `q≠⊤` | **exige `q<∞`** |
| `critical_char_radius` | `Formalizacao/AlturaCritical3.lean:556` | caracterização de raio | `1<p` | — |
| `classNH_le_sigma` | `Formalizacao/LowJackson2.lean:19` | `n≤N ⇒ classNH n H ⊆ Sigma H N` | — | — |
| `eval_lipschitz`, `terminal_affine` | `Formalizacao/AlturaTerminal.lean:88, 192` | Lipschitz e afim nas folhas terminais | `WF`, `maxHeight ≤ H` | — |
| `leaf_budget_atMost` | `RequestProject/Budgets.lean:208` | **contagem** de catálogo com `≤N` folhas | `2≤S.H` | — (não é piso) |
| `jointErr_succ_N_le`, `jointErr_succ_H_le` | `RequestProject/JointBudget.lean:55, 59` | monotonicidade em `N` e `H` do erro **uniforme** | — | — (ver GAP-014) |

**Declaração de `uniform_besov_ball` (conteúdo):** para cada `r≥1`, com `H = Hunif(32(Cs+1), B, nuHat, kapHat(κ))` e `N=2^r`, existe `g∈classNH(2^r, H(2^r))` com `distP f g ≤ E` e `E ≤ (9CW B+1)·2^{-rs}`. A cota `realP ≤ ((1+45CW)B+5/2)·2^{-rs}` também está no enunciado. **Não há** uma versão para `N` arbitrário.

### 5.3. Teoremas Lean dos regimes de conjecturas (fora do caminho crítico de 5.2)

`conj1_endpoint`, `conj1_subcritical`, `conj1_critical`, `conj1_tilde` e os análogos `conj2_*` (`LpJackson3.lean`, `Stability.lean`, `Theorems.lean`) tratam a caracterização de Besov e a estabilidade. Não entram na cadeia do Teorema 5.2 e não foram classificados individualmente. Os `conj*_of_J` de `Theorems.lean:27–90` são **condicionais** a `HypJp`; a composição com `hypJp_of_lt` está em `LpJackson3.lean` e os torna incondicionais no regime `1/p<s`.

---

## 6. Matriz LaTeX–Lean

**Legenda de classes:** A = pronto (demonstrado e fiel); B = reutilizável com adaptação (demonstrado, mas exige ponte ou generalização, incluindo constantes dependentes de `f` ou restrições de `q`); C = condicional (demonstrado sob hipótese auxiliar ainda não estabelecida); D = ausente; E = divergente.

| ID | Declaração LaTeX | Declaração Lean | Arquivo:linha | Classe | Evidência e observação |
|---|---|---|---|---|---|
| DEF-01 | `‖f‖*` (`lp:eq:besov-p`) | `besovNorm` | `UnifSup.lean:23` | A | Enunciado lido; coincide. |
| DEF-02 | índice dyádico `r≥0` | `besovSeq` | `Reductions.lean:24` | A | Índices conferidos. |
| DEF-03 | `ω_p(f,t)` (`lp:eq:modulus-p`) | `wtP` | `LpDefs.lean:30` | A | `sup` sobre `h∈(0,min(t,1/2)]`, medida em `[0,1−2h]`. |
| DEF-04 | `B^s_{p,q}` | `besovP` | `LpDefs.lean:57` | A | Coincide. |
| DEF-05 | `ℓ^q` com `q=∞` | `lqNorm` | `LpDefs.lean:44` | A | `q=⊤` ⇒ supremo. |
| DEF-06 | `‖f−g‖_p` | `distP` | `LpDefs.lean:35` | A | Coincide. |
| DEF-07 | `R_{N,H}` (`realP`) | `realP` | `LpDefs.lean:40` | A | Coincide com `lp:eq:realization-p`. |
| DEF-08 | `𝒜_{N,H}([0,1])` | `classNH` | `LpDefs.lean:64` | A | Coincide. |
| DEF-09 | `Σ_{N,H}={0}∪𝒜_{N,H}` | `Sigma` | `Pendencias/Agenda.lean:24` | A | Coincide. |
| DEF-10 | altura do segmento | `Atom.height` | `RequestProject/Atoms.lean:45` | A | Coincide com a fórmula de `[lp:sec:defs]`. |
| DEF-11 | `height(u)=max{|a|,b}` | `ht` | `RequestProject/Indexing.lean:129` | A | Coincide. |
| DEF-12 | altura máxima da árvore | `LTree.maxHeight` | `RequestProject/Trees.lean:110` | A | Coincide. |
| DEF-13 | `N` folhas e altura `≤H` | `AdmNH` | `RequestProject/JointBudget.lean:27` | A | Coincide. |
| DEF-14 | `e^H_{N,p}(f)` | `bestError` | `ArithmeticFloor.lean:145` | A | Coincide. |
| DEF-15 | `a(p,s)` | `nuHat` | `UnifTheorem.lean:40` | B | Valores coincidem em todas as faixas, mas não há `aPS` nomeada nem lema de igualdade (GAP-005). |
| DEF-16 | fator logarítmico | `kapHat` | `UnifTheorem.lean:43` | B | `θ_q+κ` em `s=1/p` introduz `log` (GAP-007/008). |
| DEF-17 | agenda `H_{s,κ}` | `Hunif` | `UnifTheorem.lean:47` | B | Usa `N+1` e `L(N)^κ`, não `(N)` exato; equivalência a `lp:eq:schedule` depende de `κ`. |
| DEF-18 | `κ q>1` (`lp:thm:uniform`) | `UniformAdmissible` | `UnifTheorem.lean:182` | A | `1/q<κ` para `s≥1`, `q<∞`. Condição só para a parte `ℓ^q`. |
| DEF-19 | `lp:hyp:jackson` com `R=‖f‖_∞` do representante contínuo | `HypJp` | `LpDefs.lean:120` | E | Usa `toReal` de sup pontual de representante arbitrário; constantes dependem de `f`. Ver GAP-013. |
| DEF-20 | `lp:hyp:jackson` (constantes `C_W`, `16`) | `HypJpStrong` | `LpJackson4.lean:19` | A | Enunciado fiel. |
| DEF-21 | `H_B(N)` linear (`lp:thm:critical-linear`) | `criticalAgenda` | `AlturaCritical3.lean:33` | A | `⌈Avc(B+1)(N+1)⌉`. |
| DEF-22 | erro `L^p` | `supDist/jointErr/leafErr` | `RequestProject/JointBudget.lean:23,30,34` | E | Norma **uniforme**. Não é o funcional do Teorema 5.2. Ver GAP-014. |
| LB-01 | `dist(a_H,𝒬_H)=1/(2H)` (`lp:prop:floor`) | `rational_arithmetic_floor` | `ArithmeticFloor.lean:35` | A | Enunciado fiel. |
| LB-02 | `‖f_H−g‖_p ≥ 1/(2H)`, `∀N`, `g∈{0}∪𝒜` (`lp:eq:floor`) | `arithmetic_floor_lp` | `ArithmeticFloor.lean:129` | A | Enunciado fiel, com `∀N`. |
| LB-03 | `e^H_{N,p}(f_H) ≥ 1/(2H)` | `arithmetic_floor_bestError` | `ArithmeticFloor.lean:148` | A | Fiel. |
| LB-04 | necessidade de altura `N^s ≲ H` | `arithmetic_height_necessary` | `ArithmeticFloor.lean:168` | A | Fora do caminho crítico de `D ≥`. |
| LB-05 | `‖f_H−g‖_p ≥ c_G H^{-s}`, `∀N`, `g∈Σ_{N,H}` (`lp:prop:geom-floor`) | `geometric_floor` | `AlturaFloor.lean:363` | A | Fiel; generalizado a `0<s<2` (ver §5.1). |
| LB-06 | ferramentas do piso geométrico | `geometric_dist_lower`, `lp_lower_of_L1`, `L1_affine_lower` | `AlturaFloor.lean:309, 261, 144` | B | Reutilizáveis para o piso de folhas (GAP-004), que precisa de bumps múltiplos. |
| LB-07 | `‖f_H−g‖_p ≥ c_L H^{-β}`, `β=s/(1+1/p−s)`, `s≤1/p` (`lp:prop:slope-floor`) | `slope_floor` | `AlturaSlope.lean:250` | A | Fiel. |
| LB-08 | escala do bump `‖bumpS‖* ≲ |a| t^{1/p−s}` | `besovNorm_bumpS_le` | `AlturaBesov.lean:252` | B | Serve para um bump; o piso de folhas precisa de soma de `2N` bumps com `K_{s,q}`. |
| LB-09 | necessidade (`lp:cor:joint-necessity`) | `geometric_/slope_/arithmetic_necessity` | `AlturaNecessity.lean:85,108,136` | A | Fora do caminho crítico de 5.2. |
| LB-10 | `D_{p,s,q}(N,H) ≥ c_leaf N^{-s}` (`lp:lem:leaf-budget-floor`) | **ausente** | — | D | Nenhuma declaração Lean com esse conteúdo. Ver GAP-002. |
| LB-11 | `C1 = c_φ + C2 K_{s,q}` (`lp:lem:packing`) | **ausente** (`EntropyLower.packing_lower` é outro objeto) | — | D | Ver GAP-003. |
| UB-01 | `WhitneyLp` (`lp:lem:whitney`) | `whitney_lp` | `Whitney12.lean:31` | A | Incondicional em `p≥1`. |
| UB-02 | `‖f−Q_nf‖_p ≤ 9C_W ω(f,1/n)` (`lp:cor:quasi-error`) | `quasi_error_unc` | `Whitney13.lean:18` | A | Incondicional. |
| UB-03 | representante contínuo (`lp:lem:embedding`) | `besov_continuous_rep` | `LpJackson4.lean:87` | B | Usado em `HypJpStrong`; depende de `1/p<s`. |
| UB-04 | `lp:hyp:jackson` | `hypJpStrong_of_lt` | `LpJackson4.lean:30` | B | Constantes uniformes em `p`, mas `n0=n0(f)`; não basta para ter uniformidade na bola. |
| UB-05 | `J_p` como premissa das Conj. | `hypJp_of_lt` | `LpJackson2.lean:152` | B | Demonstrado; constantes dependentes de `f`. |
| UB-06 | idem | `hypJp_of_lt'` | `LpJackson3.lean:19` | B | Versão em `ℝ≥0∞`. |
| UB-07 | Jackson `s≤1/p` (`lp:thm:jackson-low`) | `jackson_low` | `LowJackson2.lean:24` | B | Constantes `CW, K` dependem de `f`. |
| UB-08 | núcleo de Jackson | `lp_jackson_core` | `LpJackson2.lean:25` | B | Núcleo; `CW` como parâmetro. |
| UB-09 | núcleo para `s≤1/p` | `lp_jackson_low_core` | `LowJackson.lean:18` | B | Idem. |
| UB-10 | `lp:lem:nodal-jump` | `nodal_jump` | `AlturaCritical.lean:82` | B | Salto nodal com constantes `K_k`. |
| UB-11 | `lp:lem:nodal-general` / quantização | `quantization_jump` | `AlturaQuant.lean:21` | B | **Denominador comum** `2^r`; não há denominadores por nó. |
| UB-12 | quantização sem controle de salto | `nodal_tree_gen` | `LowNodal.lean:19` | B | Usado em `s≤1/p`. |
| UB-13 | variante grossa | `nodal_tree_coarse` | `AlturaCoarse.lean:18` | B | Idem. |
| UB-14 | `lp:lem:sup-bound` (`Λ_r`) | `lam_bound_unif` | `UnifSup.lean:138` | B | Limita amplitude nodal; uniforme. |
| UB-15 | `lp:lem:uniform-height` | `uniform_height_quantization` | `UnifTheorem.lean:205` | B | Denominador comum `Q`. |
| UB-16 | `lp:thm:uniform` | `uniform_ball_of_budget` | `UnifTheorem.lean:315` | B | Constantes uniformes; agenda genérica. |
| UB-17 | `lp:thm:uniform` (por escala) | `uniform_besov_ball` | `UnifTheorem.lean:409` | B | Cobre todo `0<q≤∞` por escala; `N=2^r` apenas; `log` em `s=1/p`, `q>1`, e em `p=s=1`, `q>1`. |
| UB-18 | `lp:thm:critical-linear` (nível) | `critical_approx` | `AlturaCritical.lean:266` | B | `p>1`, `s=1/p`. |
| UB-19 | nível crítico | `critical_level` | `AlturaCritical2.lean:90` | B | Idem. |
| UB-20 | `lp:thm:critical-linear(b)` `ℓ^q` | `critical_lq` | `AlturaCritical3.lean:311` | B | Só `q<∞`; `WhitneyLp` discharged por `whitney_lp` (GAP-015). |
| UB-21 | `lp:thm:critical-linear(b)` taxa | `critical_rate` | `AlturaCritical3.lean:514` | B | Só `q<∞`. Ausente para `q=∞` (GAP-009). |
| UB-22 | monotonicidade em `N` | `classNH_le_sigma` | `LowJackson2.lean:19` | A | `n≤N ⇒ classNH n H ⊆ Sigma H N`. Sem monotonicidade em `H` (GAP-010). |
| UB-23 | afim nas folhas terminais | `terminal_affine`, `eval_lipschitz` | `AlturaTerminal.lean:192, 88` | A | Reutilizável. |
| UB-24 | contagem de catálogo | `leaf_budget_atMost` | `RequestProject/Budgets.lean:208` | A | **Não é o piso de folhas**; é cardinalidade do catálogo. |
| UB-25 | monotonicidade do erro | `jointErr_succ_N_le`, `jointErr_succ_H_le` | `RequestProject/JointBudget.lean:55, 59` | E | Em norma uniforme. Não substitui a monotonicidade em `L^p`. |
| UB-26 | nodal com denominadores diádicos **por nó** (`lp:lem:nodal-variable-height`) | **ausente** | — | D | Nenhum teorema com denominadores por nó. `RequestProject/DP.lean` é programação dinâmica de Bellman, não quantização nodal. Ver GAP-007. |
| UB-27 | altura linear para `p=s=1`, todo `q` (`lp:prop:l1-linear-height`) | **ausente** | — | D | `uniform_besov_ball` dá altura linear só se `kapHat=κ=0`, isto é, `q≤1`. Ver GAP-008. |
| UB-28 | `s=1/p`, `q=∞` (`lp:thm:critical-linear` com `q≤∞`) | **ausente** | — | D | Ver GAP-009. |
| UB-29 | independência de `(N,H)` (proof de `lp:thm:minimax-nh`, "Orçamentos inteiros") | **ausente** | — | D | Ver GAP-010. |
| MIN-01 | `D_{p,s,q}(N,H)` e `a(p,s)` | **ausentes** | — | D | Ver GAP-001. |
| MIN-02 | `lp:thm:minimax-nh` (enunciado completo) | **ausente** | — | D | Ver GAP-001 e §17. |

**Contagem das classes (linhas da matriz, 64 no total):**

| Classe | Quantidade | Observação |
|---|---|---|
| A — pronto | 30 | incluem definições fiéis, pisos aritmético, geométrico e inclinação, Whitney, monotonicidade em `N`. |
| B — reutilizável com adaptação | 23 | inclui `uniform_besov_ball`, `jackson_low`, críticos com `q<∞`. |
| C — condicional | 0 | nenhum resultado da cadeia de 5.2 depende de hipótese ainda não estabelecida. Os `conj*_of_J` de `Theorems.lean` são condicionais a `HypJp`, mas `HypJp` é demonstrado em `LpJackson2.lean:152`; não estão na matriz. |
| D — ausente | 8 | piso de folhas, `lem:packing`, nodal com denominadores por nó, `p=s=1`, `s=1/p` com `q=∞`, independência de orçamentos, `D` e `a(p,s)` e o próprio teorema. |
| E — divergente | 3 | `HypJp` (DEF-19), `JointBudget` (DEF-22), monotonicidades de `JointBudget` (UB-25). |

Foram examinadas **63 declarações Lean individuais** (por enunciado), agrupadas em 56 linhas com implementação, mais 8 linhas de lacuna. Demonstrações foram lidas integralmente apenas onde a classificação dependia disso (`HypJpStrong`, `geometric_floor`, `uniform_besov_ball`, `critical_*`). Para as demais, a classificação se apoia no enunciado e na compilação bem-sucedida, o que é indicado na coluna de evidência.

---

## 7. Auditoria das cotas inferiores

### 7.1. F2.1 — Piso pelo número de folhas (`lp:lem:leaf-budget-floor`)

**Enunciado:** `D_{p,s,q}(N,H) ≥ c_leaf N^{-s}` para todos `N,H≥2`.

**Componentes e status:**

| Componente do manuscrito | Status Lean | Evidência |
|---|---|---|
| Função de teste `f_m = b m^{-s} Σ_j φ(mx−j)`, com `m=2N` | **Ausente** | Nenhuma soma de bumps disjuntos em `Formalizacao/`. Só existe um bump único (`bumpS`, `AlturaBump.lean:72`). |
| Normalização `‖f_m‖* ≤ 1` via `b = 1/C_1` | **Ausente** | Exige `lp:lem:packing`. `besovNorm_bumpS_le` cobre um bump, não a soma. |
| Cota `C_1 = c_φ + C_2 K_{s,q}` com `K_{s,q}` (soma em `k∈ℤ`) | **Ausente** | Só `K_{s,q}` com `q=∞` (`K=1`) e `q<∞` (soma geométrica) exigiria tsum em `ℝ≥0∞`. Não encontrado. |
| Contagem: `≤N−1` fronteiras internas ⇒ `≥m−N+1≥m/2` células afins | **Ausente** | Nenhum lema de contagem de células em árvore com `AdmNH`. |
| Integração por partes `∫L_jφ''=0`, `∫φφ''=−∫|φ'|²` | **Parcial** | Análogo em `AlturaFloor.lean:144` (`L1_affine_lower`) e `AlturaFloor.lean:222` (`L1_affine_interval`), com bump `φB`. Reutilizável. |
| Hölder com `p'` (incluindo `p'=∞` quando `p=1`) e mudança de variável | **Parcial** | `lp_lower_of_L1` (`AlturaFloor.lean:261`). |
| Ínfimo sobre `g` e `m=2N` | **Ausente** | Depende dos anteriores. |
| Uniformidade de `c_leaf` em `N,H` | a verificar em F2 | `c_leaf` depende de `(p,s,q)` pelo manuscrito; a prova em Lean precisaria mostrar isso. |
| Cobertura `q=∞` e `p=1` | a verificar em F2 | `K_{s,∞}=1` é o caso fácil; `p=1` exige `p'=∞`. |
| Árvores adaptativas | **Parcial** | `AdmNH` (`JointBudget.lean:27`) fornece `numLeaves ≤ N`, que é a hipótese necessária. |

**Último resultado certificado:** `geometric_dist_lower` e `L1_affine_lower` (cota para afim sobre bump único).
**Primeiro passo ausente:** `lp:lem:packing` (norma `B^s_{p,q}` de soma de bumps disjuntos).

### 7.2. F2.2 — Piso aritmético (`lp:prop:floor`)

**Status:** formalizado.

- `rational_arithmetic_floor` (`ArithmeticFloor.lean:35`): `infDist(1/(2H), Q_H)=1/(2H)`. O conjunto `Q_H` é `QH H = {r : ht r ≤ H}` (`Pendencias/Agenda.lean:32`), com `ht r = max |num| den`. Esta altura coincide com `height(u)=max{|a|,b}` do manuscrito (ver DEF-11).
- `arithmetic_floor_lp` (`ArithmeticFloor.lean:129`): para todo `N`, `g∈Sigma(H) N`, `ofReal(1/(2H)) ≤ distP p (const) g`. Corresponde a `lp:eq:floor`.
- A relação de alturas está verificada: o manuscrito usa `height(u)=max{|a|,b}` e a Lean usa `ht` com a mesma fórmula.

**Uso no Teorema 5.2:** cobre o piso `H^{-1}` para `s>1` (onde `a=s`, logo `H^{-s/a}=H^{-1}`).

### 7.3. F2.3 — Piso geométrico (`lp:prop:geom-floor`)

**Status:** formalizado, com enunciado fiel e mais geral (`0<s<2`).

- `geometric_floor` (`AlturaFloor.lean:363`): `∃c, ∀H≥2, ∃f, Measurable f ∧ ‖f‖*≤1 ∧ ∀N, ∀g∈Sigma(fun _↦H) N, c·H^{-s} ≤ distP p f g`.
- Elementos do manuscrito verificados: estrutura da folha terminal direita (`terminal_affine`, `AlturaTerminal.lean:192`); limitação de resolução por `H` (`eval_lipschitz`, `AlturaTerminal.lean:88`); alvo localizado (`φB`, `AlturaFloor.lean:28`); erro inferior em `L^p` (`lp_lower_of_L1`); independência do orçamento de folhas (`∀N` no enunciado).

**Uso no Teorema 5.2:** cobre o piso `H^{-s}` para `1/p≤s≤1`, onde `a=1`.

### 7.4. F2.4 — Piso por inclinação (`lp:prop:slope-floor`)

**Status:** formalizado, com enunciado fiel.

- `slope_floor` (`AlturaSlope.lean:250`): hipóteses `1≤p`, `0<q`, `0<s<2`, `s≤1/p`; conclusão `c·H^{-s/(1+(p⁻¹−s))}`. Corresponde a `β=s/(1+1/p−s)`.
- Lemas auxiliares: `two_interval_pointwise` (`AlturaSlope.lean:23`), `slope_dist_lower` (`AlturaSlope.lean:158`), `sigma_lipschitz` (`AlturaSlope.lean:234`), que dá a cota Lipschitz decorrente da altura `H`.
- Constante auxiliar `cpConst` (`AlturaSlope.lean:146`) depende só de um expoente `Q`. A constante final `c` de `slope_floor` aparece como `∃ c` antes de `H`, o que é compatível com dependência só de `(p,s,q)`. Confirmar essa dependência em F2, por leitura da prova.

**Ponto de atenção:** a demonstração de `slope_floor` usa `besovNorm_bumpS_le` com `Λ' = max Λ 1`, o que confirma que `c` não depende de `H`.

### 7.5. Resumo: último certificado e primeiro passo ausente

| Piso | Último resultado certificado em Lean | Primeiro passo ausente |
|---|---|---|
| Folhas `N^{-s}` | `geometric_dist_lower` / `L1_affine_lower` (bump único) | `lp:lem:packing` (soma de `2N` bumps) |
| Aritmético `H^{-1}` | `arithmetic_floor_lp` | nenhum para `s>1` |
| Geométrico `H^{-s}` | `geometric_floor` | nenhum para `1/p≤s≤1` |
| Inclinação `H^{-β}` | `slope_floor` | nenhum para `s<1/p` |

---

## 8. Auditoria das cotas superiores

### 8.1. Cadeia: Besov → projeção → quase-interpolante → quantização → árvore admissível → erro uniforme

| Elo | Lean | Status |
|---|---|---|
| Besov ⇒ projeção local em afins | `Q_cell`, `Q_affine` (`QuasiGrid.lean:166, 183`) | A |
| Quase-interpolante com erro `9C_W ω(f,1/n)` em `L^p` | `quasi_error_unc` (`Whitney13.lean:18`) | A (incondicional) |
| Quantização racional com denominador `2^r` | `quantization_jump` (`AlturaQuant.lean:21`) | B (denominador comum) |
| Árvore admissível `AdmNH(2^r,H)` | `classNH` / `AdmNH` | A |
| Erro uniforme na bola | `uniform_besov_ball` (`UnifTheorem.lean:409`) | B (por escala, `N=2^r`) |

### 8.2. Projeções e Jackson (item 7.1 do roteiro)

- **Núcleos afins e reprodução:** `Kernel.lean` (`kernel_is_affine_projection`, `reproduce_affine`), com status A (verificado por `#print axioms` no `Auditoria.lean`).
- **Estimativas locais:** `local_error_inf` (`Corollary54.lean`), `lam_diff_le` (`Lemma52d.lean`).
- **Desigualdade de Whitney:** `whitney_lp` (`Whitney12.lean:31`) é incondicional. `WhitneyLp p CW` é hipótese das versões críticas, e `whitney_lp` a satisfaz. Falta apenas um lema de instanciação (GAP-015).
- **Quase-interpolação:** `quasi_error_unc` (`Whitney13.lean:18`), incondicional.
- **Dependência das constantes:** `CW` depende só de `p`; `Cs` e `CW` de `uniform_ball_of_budget` não dependem de `f` nem de `B` (ver a ordem dos quantificadores em `UnifTheorem.lean:315`).

### 8.3. Análise de `HypJp`, `HypJpStrong`, `hypJpStrong_of_lt` (pedido explícito)

**Onde a uniformidade se perde:**

1. **`HypJp` (LpDefs.lean:120):** `C0, C1, n0` são escolhidos **depois** de `f` (`∀ f, … → ∃ C0 C1 …`). A prova `hypJp_of_lt` (LpJackson2.lean:152) herda essa dependência. Não serve para uma cota minimax com constantes dependentes só de `(p,s,q)`. O manuscrito reconhece isso no apêndice Lean ("constantes que podem depender de `f`").
2. **`HypJp`: `R` via `toReal` de supremo pontual.** `R=(⨆ x∈[0,1], ofReal|f x|).toReal`. Para uma função não limitada num representante, o supremo é `⊤` e `toReal ⊤ = 0`, portanto `R=0` silenciosamente. Além disso, o supremo pontual depende do representante, enquanto `lp:hyp:jackson` usa `R=‖f‖_∞` do **representante contínuo**. Isso é uma **divergência de modelagem** (GAP-013).
3. **`HypJpStrong` (LpJackson4.lean:19):** `C0, C1` são escolhidos antes de `f` (uniformes), mas `n0` é escolhido depois de `f` (`∀f … ∃n0`), conforme `lp:hyp:jackson` (`n0=n0(f,p,s)`, linha 190–199 do `.tex`). A demonstração `hypJpStrong_of_lt` usa a continuidade de `f` via `nodal_G` e `hsmall`, portanto `n0` depende do módulo de continuidade de `f`. Essa dependência **não é uniforme na bola**, e por isso `HypJpStrong` não basta para o Teorema 5.2. A alternativa é `uniform_besov_ball`, que tem constantes antes de `f`.

**Conclusão para o Teorema 5.2:** o caminho uniforme é `uniform_besov_ball` / `uniform_ball_of_budget`. `HypJp` e `HypJpStrong` servem à caracterização (Conjecturas 1 e 2), não à cota minimax.

### 8.4. Quantização nodal (item 7.2)

| Referência | Lean | Denominador | Continuidade | Inclinação não nula | Alturas | Erro |
|---|---|---|---|---|---|---|
| `lp:lem:nodal-general` | `quantization_jump` (`AlturaQuant.lean:21`) e `nodal_tree_gen` (`LowNodal.lean:19`); mapeamento a confirmar em F3 | comum | garantida por `Atom`/`LTree` | `Atom.hs : s≠0` | `maxHeight ≤ H` | `quantization_jump` |
| `lp:lem:nodal-jump` | `nodal_jump` (`AlturaCritical.lean:82`) | comum `2^{k+1}` | por construção de `Q` | — | — | `4V0/(2^r)+Σ K_k/(2^r)` |
| `lp:lem:nodal-variable-height` | **ausente** | **por nó** | — | — | — | — |

- **Denominador comum:** `quantization_jump` e `uniform_height_quantization` usam `Q=2^{qexp}` **igual para todos os nós**.
- **Denominadores por nó:** não há teorema com denominadores diádicos variáveis por nó. `RequestProject/DP.lean` trata de programação dinâmica de Bellman, não de quantização nodal (verificado pelo cabeçalho do arquivo). Por isso **não classificamos como equivalente** nenhum resultado que só cobre denominador comum (conforme o roteiro, item 7.2).
- **Controle do erro:** `quantization_jump` controla o erro por `2^r(J+1) ≤ H`, com `J` o salto máximo.

### 8.5. Casos críticos (item 7.3 e §9)

Ver §9.

---

## 9. Auditoria dos casos críticos

Para cada caso, verificamos cobertura para `0<q≤∞`.

| Caso | Lean (cota superior) | Cobertura em `q` | Lean (cota inferior) | Situação |
|---|---|---|---|---|
| (1) `0<s<1/p` | `uniform_besov_ball` (`nuHat=a`, `kapHat=0`); `jackson_low` (`s≤1/p`) | todo `q`, por escala | `slope_floor` | **Coberto por escala** (B). |
| (2) `s=1/p`, `p>1` | `critical_rate`, `critical_lq` (`criticalAgenda` linear); `uniform_besov_ball` tem `log` se `q>1` | `q<∞` apenas (`critical_*` exigem `q≠⊤`) | `geometric_floor` (`a=1`) | **Lacuna em `q=∞`** (GAP-009). Para `q<∞`, coberto por `critical_rate`. |
| (3) `p=s=1` | `uniform_besov_ball` com `kapHat=κ` (sem log) apenas se `θ_q=0`, isto é `q≤1` | `q≤1` por escala; **`q>1` tem `log`** | `geometric_floor` | **Lacuna para `q>1`** (GAP-008). A prova do manuscrito usa `lp:prop:l1-linear-height`, ausente. |
| (4) `1/p<s≤1` | `uniform_besov_ball` (`nuHat=1`, `kapHat=κ`) | todo `q` por escala | `geometric_floor` | **Coberto por escala** (B). |
| (5) `1<s<2` | `uniform_besov_ball` (`nuHat=s`, `kapHat=κ`) | todo `q` por escala | `arithmetic_floor_lp` | **Coberto por escala** (B). |

**Registro preciso de cobertura para `q≤∞`:**
- Casos (1), (4), (5): cobertos para todo `0<q≤∞` pela cota por escala.
- Caso (2): cobertura para `q<∞` (via `critical_rate`); **falta `q=∞`**.
- Caso (3): cobertura para `q≤1` (linear por `uniform_besov_ball`, `κ=0`); **falta `q>1`** (incluindo `q=∞`).

**Observação sobre `UniformAdmissible`:** essa condição (`1/q<κ` para `s≥1`, `q<∞`) só é necessária para a parte `ℓ^q` de `uniform_besov_ball`. A cota minimax usa apenas a parte por escala, que não a exige. Portanto **não é um obstáculo** para `D`.

---

## 10. Auditoria da uniformidade das constantes

| Constante | Dependência esperada | Dependência Lean | Status |
|---|---|---|---|
| `C_W` (Whitney) | `p` | `whitney_lp`, `quasi_error_unc`: `CW` depende de `p` | A |
| `C_1` (cota inferior, folhas) | `(p,s,q)` | ausente | D |
| `c_G`, `c_L`, `1/(2H)` | `(p,s,q)` | `geometric_floor`, `slope_floor`: `c` depende de `(p,s,q)` (verificado pela estrutura do `∃`) | A |
| `CW, Cs` da cota superior | `(p,s,q)` | `uniform_ball_of_budget`, `uniform_besov_ball` (`∃` antes de `κ,B,f`) | B (uniforme; falta o `N` arbitrário) |
| `C_*` (arredondamento) | `(p,s,q)` | `uniform_besov_ball` usa `Hunif(32(Cs+1),…)` | B |
| `C_E` (`l1-linear-height`) | `C_W` | ausente | D |
| constantes de `jackson_low` (`CW,K`) | dependem de `f` | `∃ CW K` depois de `hbes` | **Não uniforme** (B) |
| constantes de `hypJp_of_lt` | dependem de `f` | `∃C0 C1` depois de `f` | **Não uniforme** (B) |
| `n0` de `hypJpStrong_of_lt` | depende de `f` (como no manuscrito) | `∃n0` depois de `f` | **Não uniforme** (B) |

**Onde a uniformidade se perde:**
1. `jackson_low` e `hypJp_of_lt`: dependem de `f`. Não servem à cota minimax.
2. `hypJpStrong_of_lt`: `n0` depende de `f`. Idem.
3. `uniform_besov_ball`: uniforme na bola, mas só para `N=2^r`. A extensão a `N` arbitrário é o ponto GAP-010.
4. `kapHat` com `θ_q+κ` em `s=1/p`: a constante cresce com `log N` quando `q>1`, o que destrói a cota `N^{-s}+H^{-s/a}` sem limitar `H` por `C N` (GAP-007/008).

**Dependência de `f` a ser evitada:** toda cota final deve ter `C` antes de `f` e de `B` (ver `lp:thm:minimax-nh`: "existem `c,C>0`" antes de `N,H`, e a sup sobre `f` na definição de `D`).

---

## 11. Grafo de dependências

Notação: `[A]` pronto, `[B]` reutilizável com adaptação, `[D]` ausente, `[E]` divergente. Setas: "depende de".

### 11.1. Raiz

```
lp:thm:minimax-nh  [D]  (MIN-02)
├── D_{p,s,q}(N,H) como sup sobre a bola  [D]  (MIN-01)  ← definição a formalizar
├── a(p,s) explícito  [B]  (DEF-15 ≡ nuHat, sem lema de igualdade)
├── cota inferior  (§11.2)
└── cota superior  (§11.3)
```

### 11.2. Cadeia das cotas inferiores

```
D ≥ c(N^{-s} + H^{-s/a})
├── piso de folhas  c N^{-s}  [D]  (LB-10)
│   ├── lp:lem:packing: soma de 2N bumps com K_{s,q}  [D]  (LB-11)
│   │   └── besovNorm_bumpS_le  [B]  (LB-08)
│   ├── contagem de células afins  [D]  (GAP-004)
│   │   └── AdmNH, numLeaves ≤ N  [A]  (DEF-13)
│   └── integração por partes e Hölder  [B]  (LB-06: L1_affine_lower, lp_lower_of_L1)
├── piso de altura  c H^{-s/a}  — por faixa:
│   ├── s<1/p:      slope_floor  [A]  (LB-07)
│   ├── 1/p≤s≤1:    geometric_floor  [A]  (LB-05)
│   └── s>1:        arithmetic_floor_lp  [A]  (LB-02)
└── composição: max(piso_folhas, piso_altura) ≥ ½ soma  [D]  (GAP-006)
```

### 11.3. Cadeia das cotas superiores

```
D ≤ C(N^{-s} + H^{-s/a})
├── cota por escala  n=2^r  [B]  (UB-17: uniform_besov_ball)
│   ├── quase-interpolação  [A]  (UB-02: quasi_error_unc)
│   ├── Whitney  [A]  (UB-01: whitney_lp)
│   ├── quantização com denominador comum  [B]  (UB-15: uniform_height_quantization)
│   │   └── lam_bound_unif  [B]  (UB-14)
│   └── Jackson (1/p<s)  [B]  (UB-04/05: hypJp*)  ← não uniforme; NÃO usar
│       ou Jackson (s≤1/p)  [B]  (UB-07: jackson_low)  ← não uniforme; NÃO usar
├── críticos  s=1/p, p>1  [B]  (UB-18..21)
│   ├── q<∞: critical_rate  [B]
│   └── q=∞: ausente  [D]  (UB-28, GAP-009)
├── p=s=1  [B para q≤1, D para q>1]  (UB-27, GAP-008)
│   └── quantização com denominadores por nó  [D]  (UB-26, GAP-007)
├── independência de (N,H)  [D]  (UB-29, GAP-010)
│   ├── escolha de n=2^{⌊log2 X⌋}, X=min{N,(H/C_*)^{1/a}}  [D]
│   ├── monotonicidade de Σ em N  [A]  (UB-22: classNH_le_sigma)
│   ├── monotonicidade de Σ em H  [D]
│   ├── candidato zero para orçamentos pequenos  [A]  (Sigma contém 0)
│   └── ‖f‖_p ≤ ‖f‖*  [A]  (UnifSup.lean:39, eLpNorm_le_besovNorm)
└── sup sobre a bola  [D]  (MIN-01)
```

### 11.4. Pontes de equivalência ausentes

1. `a(p,s)` (manuscrito, por casos) ↔ `nuHat p s` (Lean): equivalência por casos, não provada como lema. **Ponte B.**
2. `D` (sup sobre `‖f‖*≤1`) ↔ `⨆ f, bestError p N H f` com `Measurable f`: ponte de definição. **Ponte D.**
3. `R=‖f‖_∞` (contínuo) ↔ `R` de `HypJp` (`toReal` pontual): **divergente** (GAP-013).

### 11.5. Caminho crítico (sequência mínima de resultados ausentes)

A sequência mínima cuja ausência impede a formalização integral, na ordem de dependência:

1. Definir `aPS p s` e `Dfun p s q N H`, e provar `aPS = nuHat` (GAP-001, GAP-005). **Sem isso, não há alvo.**
2. `lp:lem:packing` para `q∈(0,∞]` (GAP-003).
3. Piso de folhas `c N^{-s}` (GAP-002, com GAP-004).
4. Cota superior para `p=s=1, q>1` com altura linear (GAP-007, GAP-008).
5. Cota superior para `s=1/p, q=∞` com altura linear (GAP-009).
6. Independência de `(N,H)`: arredondamento e monotonicidade em `H` (GAP-010, GAP-016).
7. Composição final (GAP-006, GAP-011).

**Reutilizáveis já existentes:** `uniform_besov_ball`, `geometric_floor`, `slope_floor`, `arithmetic_floor_lp`, `whitney_lp`, `quasi_error_unc`, `terminal_affine`, `eval_lipschitz`, `classNH_le_sigma`, `besovNorm_bumpS_le`, `L1_affine_lower`, `lp_lower_of_L1`, `eLpNorm_le_besovNorm`, `critical_rate` (para `q<∞`).

**Uso de resultados condicionais no caminho crítico:** nenhum. `HypJp` e `HypJpStrong` **não** entram no caminho crítico (ver §8.3). Os `conj*_of_J` também não.

---

## 12. Lacunas formais identificadas

Prioridade: **P0** bloqueia F5 ou F2; **P1** necessária para o teorema completo, não bloqueia o início de F2; **P2** risco ou limpeza.

| ID | Enunciado necessário | Fonte LaTeX | Código Lean relacionado | Condição ausente | Impacto no Teorema 5.2 | Etapa | Prioridade |
|---|---|---|---|---|---|---|---|
| F1-GAP-001 | Definição de `D_{p,s,q}(N,H)` (sup sobre `‖f‖*≤1`, `Measurable f`, de `bestError`) e de `a(p,s)` por casos | `conjecturas_lp.tex:858–860`, `:886–892` | `ArithmeticFloor.lean:145` (`bestError`), `UnifTheorem.lean:40` (`nuHat`) | Nenhuma definição de `D`; `a` só implícito | Sem alvo formal | F2 (definições) / F5 | P0 |
| F1-GAP-002 | `lp:lem:leaf-budget-floor`: `D ≥ c_leaf N^{-s}` | `conjecturas_lp.tex:865–884` | — | Piso de folhas inexistente | Metade da cota inferior | F2 | P0 |
| F1-GAP-003 | `lp:lem:packing`: `C1 = c_φ + C2 K_{s,q}` para somas de bumps | `conjecturas_lp.tex:794–…` | `AlturaBump.lean`, `AlturaBesov.lean:252` (só um bump) | Soma de bumps disjuntos e `K_{s,q}` | Necessário para o piso de folhas | F2 | P0 |
| F1-GAP-004 | Contagem de células afins com `≤N−1` fronteiras e `m−N+1≥m/2`, e integração por partes para `L_j` | `conjecturas_lp.tex:866–884` | `AlturaFloor.lean:144, 261` (análogos) | Lema de contagem sobre `AdmNH` | Necessário para o piso de folhas | F2 | P0 |
| F1-GAP-005 | Igualdade `a(p,s) = nuHat p s` por casos | `conjecturas_lp.tex:888–892` | `UnifTheorem.lean:40` | Lema de igualdade não provado | Ponte de definição | F2 | P1 |
| F1-GAP-006 | Composição `max(piso_folhas, piso_altura) ≥ ½(soma)` por faixa de `s`, com testes independentes | `conjecturas_lp.tex:886–935` | `geometric_floor`, `slope_floor`, `arithmetic_floor_lp` | Composição não escrita | Lower bound final | F5 | P1 |
| F1-GAP-007 | Quantização nodal com denominadores diádicos **por nó** (`lp:lem:nodal-variable-height`) | `conjecturas_lp.tex:447–470` | `quantization_jump` (comum), `DP.lean` (não relacionado) | Denominador variável por nó | Necessário para `p=s=1` com `q>1` | F3 | P0 |
| F1-GAP-008 | `lp:prop:l1-linear-height`: altura linear `H ≥ C_E(B+1)n` para `p=s=1` e todo `q` | `conjecturas_lp.tex:649–665` | `uniform_besov_ball` (log se `q>1`) | Altura linear para `q>1` | Caso `p=s=1` | F3 / F4 | P0 |
| F1-GAP-009 | `critical_rate` e `critical_lq` com `q=∞` (`s=1/p`, `p>1`) | `conjecturas_lp.tex:622–648` | `AlturaCritical3.lean:311, 514` (`q≠⊤`) | `q=∞` ausente | Cobertura de `0<q≤∞` | F4 | P0 |
| F1-GAP-010 | Independência de `(N,H)`: `n=2^{⌊log2 X⌋}`, `X/2<n≤X`, monotonicidade de `Σ` em `H`, orçamentos pequenos | `conjecturas_lp.tex:886–935` | `classNH_le_sigma` (só em `N`), `uniform_besov_ball` (só `N=2^r`) | Monotonicidade em `H` e arredondamento | Regime `(N,H)` arbitrário | F4 | P0 |
| F1-GAP-011 | Ponte da cota por escala para o sup sobre a bola com constantes em `(p,s,q)` | `conjecturas_lp.tex:886–935` | `uniform_besov_ball` | Passagem de `ℝ≥0∞`/`ℝ` e do sup | Upper bound final | F4 / F5 | P0 |
| F1-GAP-012 | Uniformidade de `n0` em `hypJpStrong_of_lt` na bola | `conjecturas_lp.tex:190–199` | `LpJackson4.lean:30` | `n0=n0(f)` | Não necessário se usar `uniform_besov_ball`; risco se o plano usar `HypJpStrong` | F4 (decisão) | P2 |
| F1-GAP-013 | Alinhar `R` de `HypJp` ao `R=‖f‖_∞` do representante contínuo; eliminar `toReal` de supremo pontual de representante arbitrário | `conjecturas_lp.tex:190–199` | `LpDefs.lean:120`, `LpJackson2.lean:152` | Definição divergente | Não afeta 5.2 diretamente; afeta conj. 1–2 | revisão (fora de F2–F6) | P1 |
| F1-GAP-014 | Substituir o uso de `JointBudget` (norma uniforme) pela versão `L^p` antes de qualquer uso no Teorema 5.2 | `conjecturas_lp.tex:858–860` | `RequestProject/JointBudget.lean:23–34` | Funcional em `L^∞` | Impede reutilização direta | F4 (decisão) | P1 |
| F1-GAP-015 | Lema de instanciação `WhitneyLp p CW` por `whitney_lp` para as versões críticas | `conjecturas_lp.tex:264` (`lem:whitney`) | `Whitney12.lean:31`, `AlturaCritical3.lean` | Hipótese não instanciada | Conveniência | F4 | P2 |
| F1-GAP-016 | Lemas aritméticos: `2^{⌊log2 X⌋}`, `X/2<n≤X`, `(2^{rs})`, `ceil` de `Hunif`, potências reais | `conjecturas_lp.tex:886–935` | `Hunif` (`UnifTheorem.lean:47`) | Lemas de arredondamento | Independência de `(N,H)` | F4 | P1 |
| F1-GAP-017 | Invariância a.e. de `D` (medidas, `f` como classe) | `conjecturas_lp.tex:60–70` | `distP`, `wtP`, `besovNorm` | Não provada | Fidelidade `L^p` | F5 | P2 |
| F1-GAP-018 | Estabelecer que `geometric_floor` (`0<s<2`) é equivalente ou mais forte que `lp:prop:geom-floor` nas faixas usadas | `conjecturas_lp.tex:747–762` | `AlturaFloor.lean:363` | Documentação da generalização | Fidelidade | F5 | P2 |
| F1-GAP-019 | Módulos `Pendencias/` são importados pela biblioteca principal | — | `Formalizacao/LpDefs.lean`, `ArithmeticFloor.lean`, etc. | Governança de nomes | Risco de confusão | F6 | P2 |

**Lacunas que não são lacunas matemáticas:** `leaf_budget_atMost` é contagem e não piso (confirmado); `packing_lower` (`RequestProject/EntropyLower.lean:199`) é outro objeto e não substitui `lp:lem:packing`.

---

## 13. Possíveis divergências matemáticas

Nenhum erro matemático foi identificado na prova do Teorema 5.2 no texto `conjecturas_lp.tex`. As verificações que fizemos:

- **Orçamentos inteiros (linhas 886–935).** Verificado: com `X=min{N,(H/C_*)^{1/a}}`, `n=2^{⌊log2 X⌋}`, tem-se `n≤N`, `C_* n^a≤H`, `n^{-s}<2^s X^{-s}`, e `X^{-s} ≤ N^{-s}+C_*^{s/a}H^{-s/a}`. Esta cadeia está correta.
- **Caso `X<2`.** Verificado: `X<2` com `N≥2` implica `2^s C_*^{s/a} H^{-s/a} > 1`, de modo que o candidato zero, com erro `≤‖f‖_p≤1`, cobre o caso.
- **Piso aritmético em `s>1`.** Verificado: `H^{-s/a}=H^{-1}` quando `a=s`, e o piso `1/(2H)` dá exatamente `H^{-1}`.
- **Caso `s=1/p`, `p>1`.** Verificado: `2A(n+1)≤3An` para `n≥2`, e o erro `(r+2)/n` é `O(n^{-1/p})` porque `n^{1/p−1}(r+2)` é limitado.
- **Caso `p=s=1`.** Verificado no texto: a altura `H≥2C_E n` dá erro `≤2C_E/H≤n^{-1}`, consistente com `s=1`.

**Pontos que exigem registro (não correção):**

1. **`lp:hyp:jackson` (linhas 190–199)** declara `n0=n0(f,p,s)`. Isso é coerente com `hypJpStrong_of_lt`, mas não basta para uniformidade na bola. O texto não afirma uniformidade na bola nesse ponto, portanto não há erro, apenas a necessidade de outra via (`uniform_besov_ball`).
2. **`lp:thm:minimax-nh`** é enunciado com `c,C` dependentes apenas de `(p,s,q)`. A prova deriva `C'` de `C_W(p)`, `C_*` e `K_{s,q}`. Essa dependência está correta, mas a passagem de `C_*` (que depende de `A` e `C_E`) para `(p,s,q)` deve ser registrada em F4.
3. **Índices `r` em `besovSeq`.** Lean usa `r:ℕ` a partir de `0` (`ω(f,1)`), como o manuscrito (`r≥0`). Verificado; não há divergência.

**Divergências Lean↔manuscrito (não matemáticas no texto, mas de modelagem):**

- `HypJp` (GAP-013): `R` por `toReal` de supremo pontual.
- `JointBudget` (GAP-014): norma uniforme.

---

## 14. Plano técnico F2–F6

Cada fase lista: dependências de entrada; arquivos Lean existentes a reutilizar; módulos novos sugeridos; teoremas a implementar; riscos; critérios de conclusão; prioridade. Não atribuímos horas: o escopo é descrito pelos identificadores de lacuna e pelas declarações existentes, que é o que o diagnóstico sustenta.

### F2 — Cotas inferiores

- **Dependências de entrada:** nenhuma pendente (definições e pisos já existem).
- **Reutilizar:** `geometric_dist_lower`, `L1_affine_lower`, `lp_lower_of_L1` (`AlturaFloor.lean`); `besovNorm_bumpS_le` (`AlturaBesov.lean:252`); `AdmNH` e `classNH_le_sigma`; `Sigma` (`Pendencias/Agenda.lean:24`); `bumpS` (`AlturaBump.lean:72`).
- **Módulos novos sugeridos:**
  - `Formalizacao/Packing.lean`: `lp:lem:packing` (soma de bumps com `K_{s,q}`, `q∈(0,∞]`).
  - `Formalizacao/LeafFloor.lean`: piso `c N^{-s}` (`lp:lem:leaf-budget-floor`).
  - `Formalizacao/MinimaxDefs.lean`: `aPS p s`, `Dfun p s q N H`, e `aPS = nuHat` (GAP-001, GAP-005).
- **Teoremas a implementar:** `packing_norm_le` (cota de `‖Σ_j bumps‖*`); `leaf_floor_const` (`∀N,H≥2, D ≥ c N^{-s}`); `leaf_count_affine` (contagem de células com `numLeaves ≤ N`); `aPS_eq_nuHat`.
- **Riscos técnicos:** (a) `tsum` em `ℝ≥0∞` para `K_{s,q}` com `q<∞`; (b) `p=1` com `p'=∞`; (c) reconciliar `ℝ` e `ℝ≥0∞` no lema de empacotamento.
- **Critérios verificáveis de conclusão:** (i) `leaf_floor_const` compila sem `sorry`; (ii) `#print axioms` lista só `propext`, `Classical.choice`, `Quot.sound`; (iii) a constante `c_leaf` depende só de `(p,s,q)`; (iv) teste de regressão: `Auditoria.lean` atualizado com as novas declarações.
- **Prioridade:** P0 (início imediato, sem dependência de F3–F4).

### F3 — Quantização nodal por nó

- **Dependências de entrada:** nenhuma de F2.
- **Reutilizar:** `quantization_jump` (`AlturaQuant.lean:21`), `nodal_jump` (`AlturaCritical.lean:82`), `nodal_tree_gen` (`LowNodal.lean:19`), `terminal_affine` (`AlturaTerminal.lean:192`), `Atom` (`RequestProject/Atoms.lean`).
- **Módulos novos sugeridos:** `Formalizacao/NodalVariable.lean` (denominadores `2^{k_j}` por nó); `Formalizacao/L1LinearHeight.lean` (`lp:prop:l1-linear-height`).
- **Teoremas a implementar:** `nodal_variable_height` (quantização com denominador por nó, altura `≤ H`, erro controlado); `l1_linear_height` (`p=s=1`, todo `q`, `H≥C_E(B+1)n`).
- **Riscos técnicos:** (a) a quantização por nó precisa garantir inclinação não nula (`Atom.hs : s≠0`) e altura por nó; (b) `q>1` exige a média dos módulos dos valores nodais, que é a ideia central de `l1-linear-height`; (c) risco de a formalização reproduzir o `log` de `kapHat` em vez de eliminá-lo.
- **Critérios verificáveis de conclusão:** `l1_linear_height` com `H = ⌈C_E(B+1)n⌉` e erro `≤ C_E(B+1)/H`; `nodal_variable_height` com `AdmNH (2^r) H` para todo `q`; `#print axioms` limpo.
- **Prioridade:** P0 para `p=s=1, q>1` (GAP-007, GAP-008).

### F4 — Cotas superiores uniformes

- **Dependências de entrada:** F3 (para `p=s=1`, `q>1`); F2 não é necessária para a cota superior.
- **Reutilizar:** `uniform_besov_ball` (`UnifTheorem.lean:409`); `uniform_ball_of_budget` (`UnifTheorem.lean:315`); `uniform_height_quantization` (`UnifTheorem.lean:205`); `critical_rate` e `critical_lq` (`AlturaCritical3.lean`); `whitney_lp`, `quasi_error_unc`; `classNH_le_sigma`; `eLpNorm_le_besovNorm`.
- **Módulos novos sugeridos:** `Formalizacao/MinimaxUpper.lean`: ponte por escala (`N=2^r`) para `N` arbitrário, com arredondamento; `Formalizacao/CriticalInfty.lean`: caso `s=1/p, q=∞`.
- **Teoremas a implementar:**
  - `critical_rate_infty` (`s=1/p`, `p>1`, `q=∞`, altura linear);
  - `upper_bound_NH` (`∃C, ∀N,H≥2, D ≤ C(N^{-s}+H^{-s/a})`), com `X`, `n=2^{⌊log2 X⌋}`, monotonicidade em `H` e candidato zero;
  - `Sigma_mono_H` (monotonicidade de `Sigma` em `H`);
  - `pow2_floor_bounds` (`X/2<n≤X`).
- **Pontes necessárias (nos três regimes do expoente):**
  - regime `s<1/p`: `uniform_besov_ball` (`kapHat=0`) com `nuHat=1+1/p−s`; sem `HypJp`;
  - regime `1/p≤s≤1` e `s>1`: `uniform_besov_ball` com `nuHat=1` ou `s`;
  - caso crítico `s=1/p`: `critical_rate` (`q<∞`) e `critical_rate_infty` (`q=∞`).
- **Riscos técnicos:** (a) a ordem dos quantificadores em `uniform_besov_ball` deve ser preservada; (b) `Hunif` usa `(N+1)^ν` e não `N^ν`, o que exige cota `(N+1)≤2N`; (c) conversão `ℝ≥0∞`↔`ℝ` nas constantes.
- **Critérios verificáveis de conclusão:** `upper_bound_NH` sem `sorry`; cobertura de todo `0<q≤∞` nos cinco casos da §9; constantes sem dependência de `f`.
- **Prioridade:** P0.

### F5 — Composição do Teorema 5.2

- **Dependências de entrada:** F2 (piso de folhas), F4 (cota superior).
- **Declaração Lean-alvo proposta:**

```lean
theorem minimax_nh (p s : ℝ) (q : ℝ≥0∞)
    (hp : 1 ≤ p) (hs0 : 0 < s) (hs2 : s < 2) (hq : 0 < q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N H : ℕ, 2 ≤ N → 2 ≤ H →
      ENNReal.ofReal (c * ((N : ℝ) ^ (-s) + (H : ℝ) ^ (-s / aPS p s))) ≤ Dfun p s q N H ∧
      Dfun p s q N H ≤ ENNReal.ofReal (C * ((N : ℝ) ^ (-s) + (H : ℝ) ^ (-s / aPS p s)))
```

com `Dfun p s q N H := ⨆ (f : ℝ → ℝ) (_ : Measurable f) (_ : besovNorm (ENNReal.ofReal p) s q f ≤ 1), bestError (ENNReal.ofReal p) N H f` e `aPS` definido por casos como no manuscrito.

- **Por que esta declaração não é mais fraca:** quantifica `c,C` antes de `N,H` (ordem do manuscrito); mantém `N,H≥2`; mantém `0<q≤∞` (com `q=⊤` permitido); usa o funcional `bestError` com `Σ` de `{0}∪𝒜` (fiel); usa `aPS` por casos, não `nuHat`. Se `aPS` fosse substituído por `nuHat`, a declaração seria equivalente apenas após o lema GAP-005.
- **Lemas intermediários:** `leaf_floor_const` (F2), `slope_floor`/`geometric_floor`/`arithmetic_floor_lp` (existentes), `upper_bound_NH` (F4), `aPS_eq_nuHat` (F2).
- **Composição:** cota inferior = `max(piso_folhas, piso_altura) ≥ ½(soma)` por faixa; cota superior = `upper_bound_NH`.
- **Riscos:** (a) `ENNReal.ofReal` de potências reais com expoente negativo; (b) `Dfun` como `⨆` sobre propriedades; (c) `besovNorm ≤ 1` vs `‖f‖*≤1`.
- **Critérios:** a declaração compila; `#print axioms` limpo; nenhuma hipótese adicional além de `p,s,q`.
- **Prioridade:** P0 (depende de F2 e F4).

### F6 — Certificação final

Testes a definir (todos com critério objetivo):

| Teste | Critério |
|---|---|
| Compilação integral | `lake build Formalizacao` sem erros (já passa hoje, sem `minimax_nh`). |
| Ausência de `sorryAx` | `#print axioms minimax_nh` não lista `sorryAx`. |
| Auditoria de axiomas | `lake env lean Formalizacao/Auditoria.lean` com `diff` contra `auditoria_axiomas.txt` vazio, exceto pelas novas linhas. |
| Fidelidade TeX–Lean | cada linha da matriz §6 tem declaração Lean ou classe D explicitamente registrada. |
| Uniformidade das constantes | `minimax_nh` com `∃c C` antes de `N,H`; sem `f` em nenhuma constante. |
| Cobertura dos regimes | os cinco casos da §9 com `q=∞` e `q<∞` cobertos. |
| Ausência de hipóteses artificiais | assinatura de `minimax_nh` contém apenas `p,s,q,hp,hs0,hs2,hq`. |
| Correspondência com o teorema publicado | comparação item a item com `lp:thm:minimax-nh`. |

**Módulos novos sugeridos:** `Formalizacao/MinimaxDefs.lean`, `Packing.lean`, `LeafFloor.lean`, `NodalVariable.lean`, `L1LinearHeight.lean`, `MinimaxUpper.lean`, `CriticalInfty.lean`, `MinimaxFinal.lean`.

---

## 15. Resultados da compilação e auditoria de axiomas

### 15.1. Compilação

Comandos executados em `lean4/formalizacao`:

```
lake exe cache get        → exit 0
lake build Formalizacao   → exit 0 ("Build completed successfully (8133 jobs)")
```

A varredura do log não encontrou linhas de erro. Há avisos de linter (variáveis não usadas), que não afetam a compilação.

### 15.2. Auditoria de axiomas

O comando `lake env lean Formalizacao/Auditoria.lean` foi executado com saída em um arquivo temporário fora da árvore versionada. Resultado na seção 15.2.1 abaixo.

**15.2.1. Saída resumida de `Formalizacao/Auditoria.lean`** (comparada com `lean4/formalizacao/auditoria_axiomas.txt`):

| Verificação | Resultado |
|---|---|
| Número de consultas `#print axioms` | 201 |
| Declarações com axiomas padrão apenas (`propext`, `Classical.choice`, `Quot.sound`) | 201 de 201 |
| Ocorrências de `sorryAx` | 0 |
| Axiomas locais ou matemáticos não demonstrados | 0 |
| Saída do Lean | código de saída 0, sem mensagens de erro |
| Diferença em relação ao `auditoria_axiomas.txt` versionado | nenhuma (`diff` vazio nas linhas `depends on axioms`) |

O arquivo `auditoria_axiomas.txt` não precisou ser alterado, pois a auditoria reproduziu o snapshot versionado.

### 15.3. Varredura de `sorry`, `sorryAx`, axiomas locais e `opaque`

| Verificação | Resultado |
|---|---|
| `sorry` como código | **0 ocorrências.** A única palavra `sorry` está num comentário (`Formalizacao/AlturaBump.lean:13`, "nenhum resultado depende de `sorry`"). |
| `axiom` local (declaração) | **0** em `Formalizacao/`, `RequestProject/`, `Pendencias/`. |
| `opaque` | **0.** |
| `admit` | **0.** |
| `sorryAx` no arquivo de auditoria | 0 ocorrências (saída de §15.2.1). |

### 15.4. Interpretação

- A compilação de `Formalizacao` **não** é evidência de que o Teorema 5.2 esteja formalizado. O alvo `minimax_nh` não existe.
- Os axiomas padrão (`propext`, `Classical.choice`, `Quot.sound`) são lógica clássica e quocientes, não hipóteses matemáticas. Não há axiomas matemáticos locais.
- `HypJp` e `HypJpStrong` são **definições** (predicados), não axiomas: são provados por `hypJp_of_lt` e `hypJpStrong_of_lt`. Não há premissa não demonstrada no caminho crítico da cota superior.

---

## 16. Riscos e bloqueadores

| ID | Risco | Gravidade | Mitigação |
|---|---|---|---|
| R-1 | Não há teorema `minimax_nh` nem definição de `D`; o escopo é grande (lacunas P0). | Alta | F2 e F4 em paralelo, com definições antes (GAP-001). |
| R-2 | Soma de bumps e `K_{s,q}` com `tsum` em `ℝ≥0∞` pode ser trabalhosa. | Média | Prototipar `q=∞` antes de `q<∞`. |
| R-3 | Denominadores por nó (`nodal-variable-height`) não existem; `q>1` em `p=s=1` depende deles. | Alta | Tratar como F3 com prioridade P0. |
| R-4 | `kapHat` com `log` em `s=1/p` pode persistir se F3 não for feita. | Alta | F3 antes de F4 no caso `p=s=1`. |
| R-5 | Módulos de `Pendencias/` são importados pela biblioteca principal; nome enganoso. | Baixa | Não renomear agora (não escopo de F1). Registrar em F6. |
| R-6 | `HypJp` com `R` por `toReal` de supremo pontual pode ser um defeito de modelagem. | Média (para conj. 1–2) | Revisão em tarefa separada (GAP-013). |
| R-7 | `JointBudget` usa norma uniforme; reutilização indevida produziria resultado de outro enunciado. | Média | Não reutilizar sem GAP-014. |
| R-8 | `REBASE_HEAD` residual (`98a11b9`), não ancestral de `HEAD`. | Baixa | Não removido; sem rebase ativo. Decisão do usuário. |
| R-9 | Tempo de compilação do `lake build` (8133 jobs). | Baixa | Compilação incremental após cache. |

**Bloqueadores:** nenhum impede a auditoria. O único bloqueador de **formalização** é a ausência de `minimax_nh` e de seus lemas P0 (GAP-001 a GAP-011).

---

## 17. Critérios de prontidão para F2

F2 pode começar quando:

1. **Definições fixadas:** `aPS p s` por casos (manuscrito); `Dfun p s q N H` como sup sobre medidas `Measurable` com `besovNorm ≤ 1` de `bestError`. **Status:** decisão tomada aqui; não há alternativa arquitetural em aberto.
2. **Assinatura de `lp:lem:packing` decidida:** `q : ℝ≥0∞`, `0<q`, constante `C1(p,s,q)` com `K_{s,q}` em `ℝ≥0∞` (sem reabrir a teoria). **Status:** decidido pelo manuscrito; a forma de Lean ainda precisa de um lema técnico de `tsum`.
3. **Ponte de `nuHat` a `aPS` explicitada como lema alvo (GAP-005).**
4. **Testes de regressão definidos:** `Auditoria.lean` com `#print axioms` para cada nova declaração.

**Nenhuma decisão arquitetural fundamental está em aberto.** Os itens 2 e 3 são lemas técnicos, não decisões de modelagem.

**F2 pode começar agora.**

---

## 18. Conclusão

A auditoria F1 foi concluída com evidências verificadas:

- **Identidade e estado Git:** repositório, branch, SHA inicial, tag `editorial-v1.0` e árvore conferidos. Não há rebase ativo; o `REBASE_HEAD` residual foi documentado e preservado.
- **Compilação:** `lake build Formalizacao` passou.
- **Fidelidade:** definições de Besov, biblioteca `Σ`, altura e funcional de realização correspondem ao manuscrito. Três divergências foram registradas: `HypJp` (GAP-013), `JointBudget` (GAP-014) e a ausência de `D` e `a(p,s)` (GAP-001).
- **Cota inferior:** os pisos aritmético, geométrico e de inclinação estão formalizados. O piso de folhas `N^{-s}` está ausente (GAP-002 a GAP-004).
- **Cota superior:** `uniform_besov_ball` dá a cota por escala com constantes uniformes. Faltam a independência de `(N,H)`, os casos `p=s=1, q>1` e `s=1/p, q=∞`.
- **Teorema 5.2:** não está formalizado. O enunciado-alvo é proposto em §14 (F5) e é fiel ao manuscrito.

**F1 está concluída.** As lacunas, o caminho crítico e o plano F2–F6 estão estabelecidos com identificadores estáveis (`F1-GAP-001` a `F1-GAP-019`).

---

## Anexo A — Tabela de rastreabilidade de lacunas

| ID | Etapa | Prioridade | Lean de partida | Manuscrito |
|---|---|---|---|---|
| F1-GAP-001 | F2 / F5 | P0 | `bestError`, `nuHat` | `conjecturas_lp.tex:858–860, 886–892` |
| F1-GAP-002 | F2 | P0 | — | `:865–884` |
| F1-GAP-003 | F2 | P0 | `besovNorm_bumpS_le` | `:794–…` |
| F1-GAP-004 | F2 | P0 | `L1_affine_lower` | `:866–884` |
| F1-GAP-005 | F2 | P1 | `nuHat` | `:888–892` |
| F1-GAP-006 | F5 | P1 | `geometric_floor`, `slope_floor` | `:886–935` |
| F1-GAP-007 | F3 | P0 | `quantization_jump` | `:447–470` |
| F1-GAP-008 | F3 / F4 | P0 | `uniform_besov_ball` | `:649–665` |
| F1-GAP-009 | F4 | P0 | `critical_rate` | `:622–648` |
| F1-GAP-010 | F4 | P0 | `classNH_le_sigma` | `:886–935` |
| F1-GAP-011 | F4 / F5 | P0 | `uniform_besov_ball` | `:886–935` |
| F1-GAP-012 | F4 | P2 | `hypJpStrong_of_lt` | `:190–199` |
| F1-GAP-013 | revisão | P1 | `HypJp` | `:190–199` |
| F1-GAP-014 | F4 | P1 | `JointBudget` | `:858–860` |
| F1-GAP-015 | F4 | P2 | `whitney_lp` | `:264` (`lem:whitney`) |
| F1-GAP-016 | F4 | P1 | `Hunif` | `:886–935` |
| F1-GAP-017 | F5 | P2 | `distP` | `:60–70` |
| F1-GAP-018 | F5 | P2 | `geometric_floor` | `:747–762` |
| F1-GAP-019 | F6 | P2 | — | — |

---

## Anexo B — Diagnóstico de F1 quanto às instruções do roteiro

- **Não foi criado módulo Lean.** A verificar pelo `git status` antes do commit: apenas este relatório é novo.
- **Nenhuma demonstração existente foi modificada.** A verificar pelo `git diff --stat` antes do commit.
- **Nenhuma estimativa de esforço sem fundamentação.** As etapas são descritas pelos identificadores de lacuna.
- **Arquivos protegidos não tocados.** `conjecturas_lp*.tex`, PDFs, `.bib`, `.sty`, módulos Lean, mapas, scripts, testes, README, relatórios anteriores — intactos.
