# Relatório conclusivo E1/E2 — quatro fontes primárias (Etapa 4B.3)

Auditoria somente leitura. Nada foi alterado no manuscrito, nos PDFs, no Lean, na bibliografia ou nos branches. Nenhum commit, merge ou pull request foi criado. As propostas de redação não foram inseridas no LaTeX.

**Decisão final: B — E1/E2 substancialmente concluídos; avançar com ressalvas bibliográficas delimitadas** (seção 17).

## 1. Identificação

- Manuscrito: `/home/victor/Projetos/conjecturas lp`, branch `pesquisa-minimax-altura`, SHA `a8c52ef5b49b404aa43e150cfc223733934e5f4d`, árvore limpa. Fonte primária: `conjecturas_lp.tex`.
- Enunciado exato do Teorema 5.2 (`lp:thm:minimax-nh`, linha 883): para `1≤p<∞`, `0<s<2`, `0<q≤∞` existem `c,C>0`, dependendo só de `(p,s,q)`, com `c(N^{-s}+H^{-s/a(p,s)}) ≤ D_{p,s,q}(N,H) ≤ C(N^{-s}+H^{-s/a(p,s)})` para todos os inteiros `N,H≥2`. `D_{p,s,q}(N,H)` é o supremo, sobre a bola unitária de `‖·‖*_{B^s_{p,q}}`, de `e^H_{N,p}(f)`, e `a(p,s)` é o definido no enunciado. A biblioteca é `Σ_{N,H}={0}∪Aclass_{N,H}([0,1])`.
- Definição de altura (linhas 106–112): `height(a/b)=max{|a|,b}`; o segmento sobre `J_{k,m}` tem altura `max{2,k+1,|m|+1,height(u),height(v)}`.
- Biblioteca Determinística: `/home/victor/BIBLIOTECA FINAL FORMALIZADA ARTIGO`, commit `3854ac7125a599e4901e38338409749e9ead94b9` (existe no repositório), `artigo_2.tex` e `artigo_3.tex` lidos no commit.
- **Correção à v2:** a definição de altura do átomo na Parte IV (`artigo_3:eq:inherited-height`) é a mesma do manuscrito, `max{2,k+1,|m|+1,height(y_0),height(s)}`. A v2 dizia que a da Biblioteca era mais restritiva. Isso estava errado; a ressalva de "transferência de classes" cai: as classes `Aclass_{N,H}([0,1])` coincidem.

## 2. Os quatro PDFs

Textos extraídos com `pdftotext` e lidos diretamente. Paginação: "pág." é a página do PDF anexado; entre colchetes, a paginação impressa.

| PDF | Identidade conferida | O que foi lido | Não lido / limite |
|---|---|---|---|
| 1. Yang | arXiv:2409.00901v3, 18/jul/2025, 35 pp. | Resumo, Seção 2 (Teor. 2.1, 2.2, pág. 4), Seção 3 (Teor. 3.1, pág. 6), enunciado e discussão do Teor. 4.6 (pág. 11), referência ao Teor. 4.7 | Demonstração do Teor. 4.6 e Apêndice A não examinados em detalhe |
| 2. Cohen–Dahmen–Daubechies–DeVore | ACHA 11 (2001) 192–226, 35 pp. | Introdução, Teor. 1.1 (pág. 8 [199]), (1.18) (pág. 9 [200]), Teor. 7.1 e Cor. 7.2 (págs. 23–25 [214–216]) | Seções 4–6 (aproximação por árvores e construção dos codificadores) e apêndices só por índice |
| 3. DeVore–Popov | Trans. AMS 305 (1988) 397–414, 19 pp. (capa na pág. 1; impressa = PDF + 395) | Seção 4 inteira (Teor. 4.5 pág. 9 [404], Cor. 4.6–4.7, Teor. 4.8 pág. 11 [406]), Teor. 5.1 (pág. 13 [408]) e Cor. 5.2, Teor. 6.1 (pág. 15 [410]), Teor. 7.1 (pág. 18 [413]) | Seções 2–3 e 8 só por índice |
| 4. Kerkyacharian–Picard | ESAIM P&S 7 (2003) 239–250, 12 pp. | Resumo, Seções 1–2 (definições), Teor. 1 e Props. 2–3 (págs. 5–6 [243–244]), Teor. 2 (pág. 7 [245]), trecho de codificação | Demonstração completa do Teor. 2 e a parte de replicação em detalhe não examinadas |

**Siegel, Elbrächter et al. e Ou et al.** foram lidos nas rodadas anteriores (Elbrächter por extração direta do PDF; Siegel e Ou por leitura do HTML arXiv em ferramenta auxiliar). Ficam como fontes de segunda mão para fins de classificação.

## 3. Resumo executivo

1. Nenhum dos quatro artigos demonstra ou permite deduzir a lei de dois orçamentos do Teorema 5.2. Nenhum deles tem um parâmetro de altura aritmética (racionais de altura limitada, com endereço diádico e inclinação não nula, em funções contínuas).
2. O termo `N^{-s}` da cota superior é a estimativa direta de DeVore–Popov (Teor. 4.5) com `r=2`, mais arredondamento racional. O que o manuscrito acrescenta é todo o lado de `H`: pisos aritmético, geométrico e por inclinação contra árvores adaptativas, e a quantização nodal que os realiza.
3. A Seção 8 aplica estimativas clássicas: entropia de ordem `ε^{-1/s}` (Birman–Solomyak, Cohen et al. Teor. 1.1, Kerkyacharian–Picard Teor. 1), a desigualdade `H_ε ≤ L` entre entropia e comprimento de código, e uma contagem de bits do catálogo. Não é resultado novo de informação. Ela mostra também que a biblioteca de altura não é ótima em bits: custa `~N log H` contra `~N` de Cohen et al. e Kerkyacharian–Picard.
4. A anterioridade interna é limitada à classe `C²` e à técnica de grade alternada. A demonstração do `artigo_2:thm:joint-budget` foi reconstruída e confere (seção 10).
5. A lei `C²` conjunta é bilateral e segue da Parte II com um piso quadrático elementar (seção 11). Não é caso do Teorema 5.2, cuja hipótese é `0<s<2`.

## 4. Comparação com Yang (arXiv:2409.00901v3)

**Resultado (verbatim, pág. 4).** Teorema 2.1 (Sobolev) e 2.2 (Besov): para `0<s<∞`, `1≤p,q≤∞` (e `1≤r≤∞`), se `1/q−1/p<s/d`, então para `W,L` suficientemente grandes, `inf_{g∈NN(W,L)} ‖f−g‖_{L^p([0,1]^d)} ≤ C‖f‖_{W^{s,q}} (WL)^{-2s/d}` (resp. `‖f‖_{B^s_{q,r}}`), com `C=C(s,r,p,q,d)`. O caso `1/q−1/p=s/d` é excluído explicitamente.

**Lado inferior.** A cota `inf ≥ C(p,d,s) min{W²L²log(WL), W³L²}^{-s/d}` (eq. 2.2, pág. 5) é atribuída a Siegel (Teor. 3) e vem de limites de dimensão VC. Os enunciados de Yang são cotas superiores.

**Recurso controlado.** Largura e profundidade `(W,L)`; parâmetros reais, sem restrição aritmética nos Teoremas 2.1–2.2. O Teorema 4.6 (pág. 11) codifica vetores inteiros `x∈ℤ^N`, `‖x‖_1≤M`, por uma rede de largura `W` e profundidade `L` explícitas. É um resultado sobre implementar uma sequência de inteiros por uma rede, não sobre racionais de altura limitada em segmentos contínuos.

**Dicionário e tentativa de redução.**
- Yang: `(W,L)`, `d≥1`, classe `B^s_{q,r}` com integrabilidade `q` e erro `L^p`, aproximante: rede ReLU geral.
- Manuscrito: `(N,H)`, `d=1`, `B^s_{p,q}` com erro `L^p`, aproximante: contínua afim por partes em árvore diádica com `≤N` folhas e altura `≤H`.
- Inclusão: toda `g∈Σ_{N,H}` é realizável por uma rede de uma camada oculta com `O(N)` neurônios. A inclusão vai da biblioteca para as redes.
- Transferência da cota inferior: o limite inferior de Yang/Siegel para `NN(W,L)` com `W≈N`, `L=2` é `(N²log N)^{-s}`, mais fraco que o piso `N^{-s}` do Lema `leaf-budget-floor`. Para subclasse, o piso certo é mais forte, e a inclusão só entrega o fraco.
- Transferência da cota superior: o Teorema 2.1 exige `L≥L*` e usa redes com muitas regiões lineares; esses aproximantes não pertencem a `Σ_{N,H}`.

**Primeiro ponto de falha:** a direção da inclusão. **Natureza do obstáculo:** essencial (a classe `Σ_{N,H}` é estritamente menor em complexidade geométrica e restrita aritmeticamente; redes profundas não estão contidas nela).

**Relação:** analogia (lei de expoente ótimo para aproximação de Besov em `L^p`, outro recurso, outro aproximante). Não há redução em nenhum sentido.

## 5. Comparação com Cohen–Dahmen–Daubechies–DeVore

**Teorema 1.1 (pág. 8 [199]).** `Ω⊂ℝ^d` domínio de Lipschitz, `1≤p≤∞`, `s>d/τ−d/p`. Então `H_ε(U(B^s_q(L_τ)), L_p) ≍ ε^{-d/s}`, com constantes dependendo só de `s` e `δ:=s−d/τ+d/p`. Os autores dizem que o resultado é bem conhecido em um cubo e que seu interesse é a cota superior, provada por codificação determinística.

**Equivalência codificação–entropia (1.18, pág. 9 [200]).** Qualquer par codificador/decodificador com distorção `<ε` satisfaz `H_ε(K) ≤ R(K,E,D)`; reciprocamente uma cobertura mínima produz um codificador com `R ≤ H_ε(K)`.

**Teorema 7.1 e Corolário 7.2 (págs. 214–216).** Para `1≤p<∞`, `0<λ<p` e a bola de `B_λ(L_p)`, o par `(E_N,D_N)` tem comprimento máximo `R ≤ c_4 2^{λN}` e distorção `≤ c_5 2^{-N(1−λ/p)}`. Para `(1/τ,s)` acima da linha crítica (`δ>0`) vale o mesmo, com `λ=d/(s+d/p)`. O Cor. 7.2 dá `H_ε(U) ≤ c_6 ε^{-d/s}` e conclui por (1.18).

**Recurso controlado.** Comprimento total de código (bits) para erro `ε`. Os coeficientes de wavelets são quantizados por planos de bits dependentes do erro; as árvores são codificadas em fluxos de posição.

**Tentativa de redução ao Teorema 5.2.**
1. Dicionário: bits `R` ↔ `4N(c_H+1)` do catálogo (Prop. `lp:prop:bits`); erro `ε` ↔ `D(N,H)`.
2. Lei inferior pela entropia: se toda `f` da bola unitária é aproximada em `ε` por `Σ_{N,H}`, então `N(ε)≤|Σ_{N,H}|≤2^{4N(c_H+1)}`; com o Teor. 1.1 (cota inferior), `c(1/ε)^{1/s}≤4N(c_H+1)`, isto é `ε ≥ c'(N log H)^{-s}`.
3. Obstrução: essa cota é estritamente mais fraca que `N^{-s}` (por um fator `log^{-s}`) e **não contém nenhum termo em `H` com dependência polinomial**. A entropia enxerga `H` só por `log H`, enquanto os pisos do manuscrito dão `H^{-s/a}`.
4. Lei superior: o decodificador `D_N` produz combinações de wavelets, que não são afins por partes contínuas com racionais de altura `≤H` em folhas diádicas. Uma versão com base de Faber–Schauder aproximaria o formato, mas os teoremas de Cohen et al. não estão enunciados para ela, e os parâmetros por folha (valor central e inclinação, ambos de altura `≤H`) exigiriam o controle nodal do manuscrito.

**Natureza do obstáculo:** essencial para a parte de `H` (cardinalidade não captura a lacuna entre um alvo e o conjunto discreto de parâmetros admissíveis); técnico para a parte de `N`.

**Relação:** consequência no lado de entropia/bits (seção 9); analogia no lado de aproximação por árvores.

## 6. Comparação com DeVore–Popov

**Classes de splines (Seção 4, pág. 7 [402]).** `Π_k(r)`: polinômios por partes de grau coordenado `<r` sobre a partição diádica `D_k` (uniforme, sem continuidade). `Σ_k`: splines suaves, gerados por B-splines tensoriais de de Boor–Fix. A aproximação é `T_k(f)=Q_k(S_k(f))`, linear no sentido de partição uniforme de `2^{kd}` células, com coeficientes reais.

**Teorema 4.5 (pág. 9 [404]).** Para `0<p<∞` e `f∈L_p(Q)`: `‖f−T_k(f)‖_p ≤ C ω_r(f,2^{-k})_p`, com `C=C(r,d,p,A)`.

**Teorema 4.8 (pág. 11 [406]).** Estimativa inversa de Bernstein para `s_k(f)_p`, com `A:=min(r, r−1+1/p)`.

**Teorema 5.1 (pág. 13 [408]).** Para `0<α<A` e `0<q,p<∞`, as normas `N_1`, `N_2`, `N_3` (expressas por `s_k(f)_p`, `f−T_k`, `T_k−T_{k−1}`) são equivalentes à norma de `B^α_q(L_p)`. Logo `B^α_q(L_p)` coincide com a classe de aproximação por splines diádicos em `L_p`.

**Restrições relevantes.** Coeficientes reais; partição uniforme (a classe de aproximação não-linear/adaptativa é tratada em outro trabalho). A caracterização vale para `α<A`. Para `r=2` e `p≥1`, `A=min(2,1+1/p)=1+1/p`. Assim, a caracterização por splines contínuos lineares por partes do Teorema 5.1 não cobre `1+1/p≤s<2`; o manuscrito cobre `0<s<2` pelo funcional de realização, que soma o módulo de segunda ordem do aproximante (`lp:prop:transfer`, `lp:cor:inclusion`). Confiança média: li a definição de `A` e o enunciado; não verifiquei se há restrição adicional na Seção 5.

**Reconstrução formal da distinção (splines reais contra átomos racionais).**
- Dado `f` e `n=2^k`, o `T_k(f)` de DeVore–Popov (com `r=2`) é uma função contínua afim por partes na malha uniforme, de nós `j/n` e valores nodais reais `λ_j(f)` (quasi-interpolante).
- O manuscrito exige, folha a folha, um segmento `u+v(x−x_{k,m})` com `u,v∈ℚ`, `v≠0` e altura `≤H`. Isso impõe: (i) `|u|≤H`, `|v|≤H`, denominadores `≤H`; (ii) nó terminal direito com `2^k≤H`; (iii) continuidade entre folhas.
- Substituir `λ_j(f)` por racionais mais próximos de altura `≤H` produz erro de arredondamento `≳1/H` (piso aritmético, `lp:prop:floor`) e exige `H≳n^{a(p,s)}` para preservar `n^{-s}`. Nenhum dos Teoremas 4.5, 4.8, 5.1 contém essas restrições.

**Pergunta de DeVore–Popov ao Teorema 5.2.**
- Termo `N^{-s}` superior: **dedutível** de Teor. 4.5 (`r=2`) + arredondamento racional (manuscrito, `lem:nodal-general`).
- Termo `N^{-s}` inferior: DeVore–Popov não dá limite inferior para árvores adaptativas; o manuscrito prova por bumps e contagem de `N−1` fronteiras (`lem:leaf-budget-floor`). O fato é clássico em aproximação não linear (larguras não lineares; DeVore–Howard–Micchelli, não lido).
- Termo `H^{-s/a}`: não contido.

**Relação:** consequência para `N^{-s}` (superior); contribuição própria para a parte de `H`.

## 7. Comparação com Kerkyacharian–Picard

**Definições (págs. 3–4).** "Besov bodies" multiescala `B^s_{π,r}` definidos por normas de coeficientes numa família `E={ψ_{j,k}}` com `Card(Λ_j)≍2^{jd}` e propriedade (1) de estabilidade em `ℓ^p`. A Observação 1 diz que coincidem com os Besov clássicos quando `E` é uma base de wavelets compactamente suportada normalizada em `L^p`. Proposição 1: `δ:=s−d(1/π−1/p)_+>0` implica `B^s_{π,r}⊂X`.

**Teorema 1 (Birman–Solomyak, pág. 5 [243]).** Para `0<p≤∞`, `0<s<∞`, `0<π≤∞`, `0<r≤∞`, com `δ>0`: existem `c,C` com `c ε^{-d/s} ≤ H(ε,U^s_{π,r},X) ≤ C ε^{-d/s}`. O artigo apresenta nova prova; as constantes explícitas são dadas e declaradas não ótimas.

**Proposição 2 (pág. 5).** Cota inferior `H(ε,U) ≥ c(s,π,r) ε^{-d/s}`. A prova usa o hipercubo `A_j={2^{-j(s+d/p)}Σ δ_kψ_{j,k}, δ_k∈{0,1}}` e uma redução a `H(·,Ω_{2^{jd}},ℓ^1)`. Observação: a leitura literal "para todo `ε>0`" é incompatível com `N(ε)=1` para `ε` maior que o raio da bola em `X`; a prova constrói uma sequência `ε_j→0`, logo o enunciado vale para `ε` pequeno. Isso é uma observação sobre a forma do enunciado, não uma inconsistência bibliográfica: a atribuição a Birman–Solomyak, o enunciado do Teorema 1 e a relação com o manuscrito são consistentes.

**Proposição 3 (págs. 5–6).** `Ω_n={0,1}^n` com distância `ℓ^1`: `H(n/4,Ω_n,ℓ^1) ≥ n/(8 log 2)`. É o lema de Varshamov–Gilbert, demonstrado por probabilidade (desigualdade de Hoeffding).

**Teorema 2 (pág. 7 [245]).** Para `f` na bola de `B^s_{π,∞}`, `card{|β_{j,k}|≥λ}≤D_1 λ^{-q}` com `d/q=s+d/p`, e `‖f−Q_λ(f)‖_X≤D_2 λ^{sq/d}`.

**Codificação replicante.** A seção de codificação (pág. 9) explica por que alocar um número fixo de bits por endereço e por coeficiente introduz um fator `log(1/ε)` indesejado, e o elimina codificando dinamicamente: sinal, valor quantizado `[|β|/λ]`, diferença entre endereços sucessivos, com separador `01` e replicação de bits.

**Observação da Seção 8 do manuscrito.** O manuscrito afirma que a aplicação dos resultados de Birman–Solomyak, citados por `[KP2003, Teorema 1]`, ao espaço definido por módulos de suavidade depende de uma equivalência de normas que não é verificada nele. Isso é correto: o Teorema 1 vale para os `B^s_{π,r}` definidos por coeficientes; a equivalência com a definição por módulos vale para wavelets suficientemente regulares (Observação 1 de K–P), e o manuscrito não a usa.

## 8. Tentativas de redução ao Teorema 5.2

Para cada fonte, passos 1–6 do procedimento (formalização, tradução, inclusão, transferência, obstrução, classificação).

| Fonte | Formalização | Tradução `(N,H,p,s,q)` | Inclusão | Transferência | Primeiro ponto de falha | Natureza |
|---|---|---|---|---|---|---|
| Yang Teor. 2.1/2.2 | Rede `(W,L)`, erro `(WL)^{-2s/d}` | `d=1`, `N` folhas ↔ `W²L` parâmetros? | `Σ_{N,H}↪NN(O(N),2)` | Superior: exige `L≥L*`, fora de `Σ`. Inferior: dá `(N²log N)^{-s}`, mais fraco | Direção da inclusão | Essencial |
| CDDD Teor. 1.1 / 7.1 / (1.18) | Entropia e codificador por árvore de wavelets | bits `R` ↔ `4N(c_H+1)` | `Σ_{N,H}` é catálogo finito de cardinalidade `≤2^{4N(c_H+1)}` | Inferior: `ε≳(N log H)^{-s}`. Superior: decodificador não produz elementos de `Σ` | Entropia vê `H` só por `log H` | Essencial (para `H`) |
| DeVore–Popov Teor. 4.5 | `‖f−T_k f‖_p≲ω_r(f,2^{-k})_p`, real | `N=2^k`, `r=2` | `Σ_{n,∞}` ⊃ `T_k` contínuo (após arredondamento) | Superior `N^{-s}`: sim | Coeficientes reais: nenhuma restrição de altura | Essencial para `H`; técnico para `N` |
| K–P Teor. 1, Props. 2–3, Teor. 2 | Entropia `ε^{-d/s}`; hipercubo; quantização por limiar | bits ↔ `L` | Classe de Besov por coeficientes | Seção 8 do manuscrito: instância direta | Não se aplica ao `H`-termo | — |
| Elbrächter (rodada anterior) | Conectividade `M`, pesos com `O(log ε⁻¹)` bits, `L²` | — | Não | Não há redução entre orçamentos | Orçamento único e norma `L²` | Essencial |

**Sobre `b∼log₂H`.** A relação não foi usada como equivalência em nenhuma tentativa. A única conversão formal utilizada foi a contagem do catálogo (`4N(c_H+1)` bits para `Σ_{N,H}`, Prop. `lp:prop:bits`), que fornece uma desigualdade entre cardinalidade e código, não uma redução da lei.

## 9. Auditoria da Seção 8

Verificadas, com recomputação das constantes:

- **`lp:lem:packing` (empacotamento de Besov).** (i) `‖f_θ‖*≤B` para `f_θ=(B/C_1)m^{-s}Σθ_jφ(mx−j)`, `0<s<2`, por majoração dos módulos de segunda ordem em torno da escala `m^{-1}` (`a_r≤C_2 a 2^{-θ_*|r−R|}`, `θ_*=min{s,2−s}`). (ii) distância `‖f_θ−f_η‖_p=(B/C_1)c_φ m^{-s-1/p}d_H^{1/p}` por suportes disjuntos. (iii) `Θ_m⊂{0,1}^m` com `|Θ_m|≥2^{m/6}`, `d_H≥m/4`, por conjunto maximal e limite de volume com `H(1/4)<5/6` (usa `3^9>2^{14}`).
- **`lp:prop:entropy-lower`.** Para `0<ε≤ε_0B`, `log_2𝒩(ε,B^s_{p,q}(B),L^p)≥c_4(B/ε)^{1/s}` com `c_4=(1/12)(c_3/(2C_1))^{1/s}`. Conferido: `Λ=c_3B/(2C_1ε)`, `m=⌈Λ^{1/s}⌉−1`, `m^s<Λ`, `m≥Λ^{1/s}/2`, separação `c_3(B/C_1)m^{-s}>2ε`. A condição `Λ≥2^s` equivale a `ε≤ε_0B`.
- **`lp:cor:bits-lower`.** `L≥c_5N−1` com `c_5=c_4(B/C_B)^{1/s}`, sob `C_BN^{-s}≤ε_0B`. A contagem `|Im D|≤2^{L+1}−1` confere.
- **`lp:obs:entropy`.** Correta: para `ε≥B`, `𝒩(ε)=1`; a proposição não cobre `ε_0B<ε<B`; a cota superior da entropia não é demonstrada.

**Comparação com os antecedentes.**
- `lem:packing`(iii) é o lema de Varshamov–Gilbert (K–P Prop. 3, via Hoeffding; o manuscrito por volume). Item (i): hipercubo de bumps com controle por `ω_2`, análogo ao `A_j` de wavelets de K–P Prop. 2, com a norma de Besov definida por módulos.
- `entropy-lower`: ordem `ε^{-1/s}` é K–P Teor. 1 / CDDD Teor. 1.1 / Birman–Solomyak; o manuscrito reprova a cota inferior com constantes explícitas para a definição por módulos.
- `bits-lower`: é a desigualdade `H_ε≤L` de K–P (Seção 1.2: `H≤L≤H+1`) e (1.18) de Cohen et al., combinada com a cota inferior de entropia.
- `prop:bits`: contagem de bits do catálogo; ver abaixo.

**Classificação:** `lem:packing` e `entropy-lower` são demonstrações alternativas ou adaptações de resultados clássicos (B); `bits-lower` é instância direta (B); `prop:bits` é adaptação ao catálogo aritmético (B). **Não se reivindica originalidade para a ordem clássica da entropia.**

**Contribuição específica da Seção 8.** A aplicação ao catálogo finito `Σ_{N,H}`: a Prop. `lp:prop:bits` limita `log_2|Σ_{N,H}|≤4N(c_H+1)`. Com `H≍N^{a}`, o catálogo tem `~N log N` bits contra `~N` pela cota de entropia (e pelos codificadores de Cohen et al. Teor. 7.1 e K–P). Portanto a biblioteca de altura **não atinge a ordem ótima de bits**: perde um fator `log N`, exatamente o efeito de "alocação fixa de bits por endereço e valor" que K–P descrevem e eliminam com codificação dinâmica. O manuscrito já omite a afirmação bilateral (Observação `obs:entropy`); convém dizer explicitamente que a lacuna é `log N`.

## 10. Anterioridade interna (E2)

**Reconstrução da demonstração de `artigo_2:thm:joint-budget`** (commit `3854ac7`, linhas ~620–740). Verificada passo a passo:
- Grades alternadas `G_j=Δ(ℤ+(j mod 2)/2)`, `Δ=n^{-2}`: valor nodal `v_j` mais próximo de `f(t_j)`, `|v_j−f(t_j)|≤Δ/2`; grades vizinhas disjuntas, logo `v_{j+1}≠v_j`.
- Erro: interpolação linear `≤M/(8n²)` mais perturbação nodal `Δ/2=1/(2n²)=4/(8n²)`; total `(M+4)/(8n²)`.
- Denominador comum `2n²`: `v_j=b_j/(2n²)`, `b_j≡j (mod 2)`, `|b_j|≤2Rn²+1`.
- Valor central `(b_j+b_{j+1})/(4n²)`: altura `≤4(R+1)n²`. Inclinação `(b_{j+1}−b_j)/(2n)`: numerador ímpar, fração reduzida e não nula; `|v_{j+1}−v_j|≤C_0/n+1/n²` (Lema da derivada: `‖f'‖∞≤4R+M/2` por Taylor em `a∈{0,1}`), logo `|b_{j+1}−b_j|≤2C_0n+2` e altura `≤2(C_0+1)n`.
- Altura do átomo: `k+1=r+1≤n`, `|m|+1≤n`, `2≤C_Hn²`, logo `≤C_Hn²` com `C_H=max{4(R+1),2(C_0+1)}`.
- Caso `N` geral: `n=2^{⌊log_2N⌋}`, `N/2<n≤N`, erro `<(M+4)/(2N²)`, altura `≤C_HN²`.

Conclusão: o resultado da Parte II é um teorema com demonstração correta, e é anterior ao manuscrito. O enunciado `artigo_2:eq:joint-all-N` é na diagonal `H=⌈C_HN²⌉`; a parte dyadic permite orçamentos independentes (seção 11).

**Técnicas herdadas.** A **grade alternada** (paridade `b_j≡j mod 2` para garantir inclinação não nula) reaparece no manuscrito em `lp:lem:nodal-general` e `lp:lem:nodal-jump` (escolha de `b_j` de paridade `j mod 2`). É técnica da Parte II. O Lema `lp:lem:nodal-variable-height` troca a paridade por três candidatos e denominadores `Q_j` por nó, uma variação do mesmo princípio.

**O que a Biblioteca antecipa e o que não antecipa.**
- Antecipa: átomos racionais com altura, endereçamento diádico, malha uniforme `H≥n`, Jackson racional em norma uniforme com denominador comum, piso aritmético (`1/(2H)`), barreira geométrica para malha uniforme (Parte IV: "a barreira geométrica da realização por malha uniforme... métodos adaptativos possuem distribuições de folhas distintas"), funcional de realização, deslocamento diádico, e a lei `C²` superior.
- Não antecipa: espaços de Besov em `L^p`, toda a faixa `0<s<2`, a transição `s=1/p`, pisos válidos contra **árvores adaptativas** (a barreira geométrica da Parte IV é para a malha uniforme), a quantização variável por nó, o endpoint `p=s=1` com altura linear, a agenda linear fixa e o crescimento no raio.

## 11. Lei conjunta `C²` (`F_{R,M}`, `R,M>0`)

**Cota superior para `(N,H)` independentes** (`N≥2`, `H≥2`). Para `H≥4C_H`: seja `n` a maior potência de dois com `n≤min{N,√(H/C_H)}`; então `n≥2` e `n>min{N,√(H/C_H)}/2`. A montagem `g_n` do teorema dyadic tem `n≤N` folhas e altura `≤C_Hn²≤H`, logo pertence a `Aclass_{N,H}` e `‖f−g_n‖∞≤(M+4)/(8n²)<(M+4)/2·max{N^{-2},C_H/H}≤C_+(N^{-2}+H^{-1})`, com `C_+=(M+4)/2·max{1,C_H}`. Para `2≤H<4C_H`: `g(x)=(x−1/2)/H` tem uma folha (raiz), altura `max{2,1,1,1,H}=H` (`height(0)=1`, `height(1/H)=H`), `|g|≤1/(2H)≤1/4`, logo `‖f−g‖∞≤R+1/4≤(R+1/4)·4C_H·H^{-1}`.

**Piso quadrático.** `f(x)=λx²`, `λ=min{R,M/2}`: `‖f‖∞=λ≤R`, `‖f''‖∞=2λ≤M`, logo `f∈F_{R,M}`. Em `[-h,h]`, o melhor polinômio de grau `≤1` para `x²` em `L∞` tem erro `h²/2` (`x²−1/2=T_2(x)/2` alterna em `−1,0,1`; teorema da equioscilação). Em um intervalo de comprimento `ℓ`, o erro é `λℓ²/8`. Toda árvore com `≤N` folhas tem folha de comprimento `≥1/N`, onde o aproximante é afim: `E_{N,H}(f)∞≥λ/(8N²)`, para todo `H`.

**Piso aritmético.** `f≡1/(2H)` pertence a `F_{R,M}` somente se `1/(2H)≤R`, isto é `H≥⌈1/(2R)⌉=:H_R`. Para `H<H_R` a constante não é admissível na classe. Para `H≥H_R`, a `lp:prop:floor` dá `‖f−g‖_p≥1/(2H)` para todo `g∈{0}∪Aclass_{N,H}`; como `‖·‖_p≤‖·‖∞` em `[0,1]`, vale em `L∞`. As classes coincidem (seção 1), então a transferência é direta.

**Teorema.** Para `N≥2`, `H≥max{2,H_R}`, `c=min{λ/16,1/4}`: `c(N^{-2}+H^{-1})≤E_{N,H}(F_{R,M})≤C_+(N^{-2}+H^{-1})`, pois `max{a,b}≥(a+b)/2`. A cota superior vale para todo `H≥2`. Constantes uniformes em `(N,H)` e dependendo só de `(R,M)`.

**Estatuto.** É consequência da Parte II (teor. dyadic) e do piso quadrático elementar. Não é caso do Teorema 5.2: a classe é `C²`, não `B^s_{p,q}` com `s<2`. A fórmula `N^{-s}+H^{-s/a}` com `a=s` em `s=2` dá `N^{-2}+H^{-1}`, consistente, mas o manuscrito não afirma isso e a classe é diferente.

## 12. Regimes críticos e demais resultados

- **`lp:lem:nodal-variable-height`.** Prova relida, sem falhas (candidatos por pigeonhole `3>2` nos nós ímpares; alturas `|b_i|≤3Dw`, valor central `≤6Dw≤H`, inclinação inteira não nula quando `D<n`, ou fração `(b_{j+1}−b_j)/(D/n)` quando `n≤D`; erro `L^1` por interpolação dos módulos nodais). A técnica é variação da grade alternada da Parte II, com denominadores por nó controlados pelo peso `w_j=1+J+|y_j|`. Analogia (não redução) com a codificação dinâmica de K–P: ambas evitam o logaritmo alocando precisão de acordo com a magnitude local, mas K–P controla comprimento de código e o manuscrito controla altura de racionais em funções contínuas. **C.**
- **`lp:prop:l1-linear-height`** (Prop. "altura linear para o erro em `B^1_{1,q}`"). Segue de `lem:critical-jump` (`p=1`) e `lem:nodal-variable-height`. Elimina o fator logarítmico **na taxa por escala**, para todo `q`. Não resolve a caracterização global para `q<∞` (Observação `lp:obs:critical-scope` o diz). **C.**
- **`lp:thm:critical-fixed-agenda`** (Teor. 7.1). Prova reverificada: `d=2^e` com `A_*d≥2A(B+1)`, `H_*(dn)≥H_B(n)`, árvores de `Σ_{n,H_B(n)}` pertencem a `Σ_{dn,H_*(dn)}`, `R_{dn}(f)≤R_n(f)` pela monotonia do módulo em `t`, reindexação e bloco inicial por `g=0`. A constante depende de `B` (portanto de `f`): igualdade de conjuntos, não equivalência de quase-normas. Consequência direta de `lp:thm:critical-linear` e do deslocamento diádico. **B.**
- **`lp:prop:critical-radius-growth`** (Prop. 7.2). Superior: `d^{1/p}(B+1)` com `d≍B`. Inferior para `f_K≡K`: `|g|≤3H/2≤K/2` quando `M≤K/(3(A_*+1))`, donde `Ξ(f_K)≳K^{1+1/p}`. O expoente `1+1/p` resulta do produto de `M^{1/p}` (fator de escala dyadica) por `K`, com `M≳K/A_*` forçado por `|g|≲H`: é escalonamento de amplitude para agendas lineares, não propriedade específica da altura aritmética. **B** (argumento); a conclusão quantitativa segue dele.
- **`lp:thm:critical-linear`** (agenda linear em `s=1/p`, `p>1`). Prova lida; ligada a `lem:critical-jump`. Sem antecedente nas quatro fontes. **C** (confiança média-baixa).

## 13. Matriz final de originalidade

Classes: A anterioridade equivalente; B consequência direta; C contribuição adicional substantiva; D candidato original; E indeterminado.

| Resultado do manuscrito | Fonte mais próxima | Teorema anterior | Redução matemática | Diferença efetiva | Classe | Confiança |
|---|---|---|---|---|---|---|
| Teor. 5.2, termo `N^{-s}` superior | DeVore–Popov | Teor. 4.5 (pág. 9 [404]), `r=2` | Sim, com arredondamento racional | Quantização nodal sob altura | B | Alta |
| Teor. 5.2, piso `N^{-s}` (`lem:leaf-budget-floor`) | Larguras não lineares (DeVore–Howard–Micchelli, não lido) | — | Não verificada | Prova própria por bumps, árvores adaptativas, `p,s,q` | E (antecedente) | Média |
| Teor. 5.2, termo `H^{-s/a}`, pisos aritmético / geométrico / inclinação | Parte IV (piso aritmético; barreira geométrica uniforme) | `artigo_3` Parte IV | Parcial: só `H^{-1}` (`s>1`) e malha uniforme | Pisos válidos contra árvores adaptativas; piso por inclinação (`s<1/p`) novo | C | Média |
| Teor. 5.2 (lei bilateral, dois orçamentos, `0<s<2`) | Yang, CDDD, DeVore–Popov, K–P, Elbrächter | Ver seção 8 | **Nenhuma**: obstruções essenciais | Dois orçamentos independentes sobre aproximação adaptativa com altura | C | Média |
| `lp:cor:minimax-realization` (Cor. 5.4) | Teor. 5.2 + `lp:prop:transfer` | — | Sim | Realização | B | Alta |
| `lp:lem:nodal-general` / `nodal-jump` | Parte II (grade alternada) | `artigo_2:thm:joint-budget` | Sim (paridade, denominador comum) | Estimativa em `L^p` por células | B | Média-alta |
| `lp:lem:nodal-variable-height` (Lema 3.9) | Parte II; K–P codificação dinâmica (analogia) | — | Não | Denominador por nó, `L^1` pela média | C | Média |
| `lp:prop:l1-linear-height` (Prop. 3.19) | — | — | Não | Remoção de `log` na taxa por escala | C | Média |
| `lp:thm:critical-linear` | Parte IV (agenda crítica citada) | — | Não | Agenda linear em `s=1/p` | C | Média-baixa |
| `lp:thm:critical-fixed-agenda` (Teor. 7.1) | `lp:thm:critical-linear` | — | Sim | Agenda fixa; igualdade de conjuntos | B | Média-alta |
| `lp:prop:critical-radius-growth` (Prop. 7.2) | Escalonamento `|g|≲H` | — | Sim | `B^{1+1/p}` | B | Média-alta |
| `lp:lem:packing` (Lema 4.8) | K–P Props. 2–3; Varshamov–Gilbert | K–P págs. 5–6 | Sim (instância) | Bumps com `ω_2`, `0<s<2`, constantes explícitas | B | Alta |
| `lp:prop:entropy-lower` | K–P Teor. 1; CDDD Teor. 1.1; Birman–Solomyak | K–P pág. 5; CDDD pág. 8 | Sim (cota inferior) | Definição por módulos; `ε≤ε_0B` | B | Alta |
| `lp:cor:bits-lower` | K–P Seção 1.2; CDDD (1.18) | `H_ε≤L` | Sim | Constantes; palavras de comprimento `≤L` | B | Alta |
| `lp:prop:bits` | Contagem; CDDD, K–P (comparação) | — | Sim | Catálogo `Σ_{N,H}`: `4N(c_H+1)` bits; perde `log N` | B | Alta |
| Lei `C²` conjunta | Parte II | `artigo_2:thm:joint-budget` (dyadic) | Sim (seção 11) | Piso quadrático; lei bilateral | B | Média-alta |

Nenhum resultado foi marcado D: nas fontes examinadas não foi encontrada redução ao Teorema 5.2, mas a classe D exigiria busca mais ampla (seção 17).

## 14. Textos propostos para a introdução (não inseridos)

**Português.**

> A aproximação de funções de Besov por splines diádicos e sua caracterização por taxas de aproximação remontam a DeVore e Popov \citep{artigo_2-devorepopov1988}, cuja estimativa direta fornece o termo $N^{-s}$ da cota superior deste trabalho. A aproximação por árvores adaptativas e a codificação ótima de bolas de Besov foram estudadas por Cohen, Dahmen, Daubechies e DeVore \citep{lp-cohen2001}, e a entropia métrica dessas bolas, de ordem $\varepsilon^{-1/s}$ no caso unidimensional, é o resultado clássico de Birman e Solomyak, reobtido por Kerkyacharian e Picard \citep{lp-kerkyacharianpicard2003}; a Seção~\ref{lp:sec:bits} aplica esses resultados ao catálogo finito de funções de altura limitada. Para redes ReLU, as taxas ótimas em função de largura e profundidade foram obtidas por Siegel \citep{lp-siegel2023} e Yang \citep{lp-yang2024}, e a otimalidade de Kolmogorov com pesos quantizados, em $L^2$ e com um único orçamento de conectividade, por Elbrächter et al. \citep{lp-elbrachter2021}. Esses trabalhos não impõem restrições aritméticas aos coeficientes nem tratam árvores adaptativas com altura racional limitada. A Parte~IV de \citet{lp-oliveiravol}, que desenvolve a biblioteca racional de segmentos afins, já estabelece o Jackson racional em norma uniforme com denominador comum, um piso aritmético e, na classe $C^2$, a estimativa conjunta com altura da ordem do quadrado do número de folhas (Parte~II). Este artigo trata a norma $L^p$ e as classes $B^s_{p,q}$, $0<s<2$, com dois orçamentos independentes: o número $N$ de folhas e a altura aritmética $H$. Demonstramos que o erro de pior caso na bola unitária tem ordem $N^{-s}+H^{-s/a(p,s)}$, com cotas inferiores válidas contra árvores adaptativas, e tratamos separadamente o regime crítico $s=1/p$ e o ponto $p=s=1$.

**Inglês.**

> Approximation of Besov functions by dyadic splines and the characterization of Besov spaces by approximation rates go back to DeVore and Popov \citep{artigo_2-devorepopov1988}; their direct estimate yields the $N^{-s}$ term of our upper bound. Tree approximation and optimal encoding of Besov balls were studied by Cohen, Dahmen, Daubechies and DeVore \citep{lp-cohen2001}, and the metric entropy of these balls, of order $\varepsilon^{-1/s}$ in dimension one, is the classical result of Birman and Solomyak, reproved by Kerkyacharian and Picard \citep{lp-kerkyacharianpicard2003}; Section~\ref{lp:sec:bits} applies these results to the finite catalogue of functions of bounded height. For ReLU networks, optimal rates in terms of width and depth were obtained by Siegel \citep{lp-siegel2023} and Yang \citep{lp-yang2024}, and Kolmogorov optimality with quantized weights, in $L^2$ and with a single connectivity budget, by Elbrächter et al. \citep{lp-elbrachter2021}. These works impose no arithmetic restriction on the coefficients and do not treat adaptive trees with bounded rational height. Part~IV of \citet{lp-oliveiravol}, which develops the rational library of affine segments, already establishes rational Jackson estimates in the uniform norm with a common denominator, an arithmetic floor, and, on the class $C^2$, the joint estimate with height of the order of the square of the number of leaves (Part~II). The present article treats the $L^p$ norm and the classes $B^s_{p,q}$, $0<s<2$, with two independent budgets: the number $N$ of leaves and the arithmetic height $H$. We show that the worst-case error on the unit ball is of order $N^{-s}+H^{-s/a(p,s)}$, with lower bounds valid against adaptive trees, and we treat the critical regime $s=1/p$ and the point $p=s=1$ separately.

As chaves `lp-cohen2001` e `lp-elbrachter2021` ainda não existem em `conjecturas_lp_referencias.tex`.

## 15. Referências e BibTeX proposto

Presentes na bibliografia do manuscrito: DeVore–Popov 1988 (`artigo_2-devorepopov1988`), DeVore–Popov 1988b, Kerkyacharian–Picard (`lp-kerkyacharianpicard2003`), Siegel (`lp-siegel2023`), Yang (`lp-yang2024`), Parte IV (`lp-oliveiravol`). **Ausentes:** Cohen et al. e Elbrächter et al.

```bibtex
@article{lp-cohen2001,
  author  = {Cohen, Albert and Dahmen, Wolfgang and Daubechies, Ingrid and DeVore, Ronald},
  title   = {Tree approximation and optimal encoding},
  journal = {Appl. Comput. Harmon. Anal.},
  volume  = {11},
  number  = {2},
  pages   = {192--226},
  year    = {2001},
  doi     = {10.1006/acha.2001.0336}
}

@article{lp-elbrachter2021,
  author  = {Elbr{\"a}chter, Dennis and Perekrestenko, Dmytro and Grohs, Philipp and B{\"o}lcskei, Helmut},
  title   = {Deep neural network approximation theory},
  journal = {IEEE Trans. Inf. Theory},
  volume  = {67},
  number  = {5},
  pages   = {2581--},
  year    = {2021},
  note    = {arXiv:1901.02220; p{\'a}gina final a confirmar}
}
```

Formato do repositório (`\abntref{...}`), equivalente para Cohen et al.: `\abntref{lp-cohen2001}{\MakeUppercase{Cohen}, A.; \MakeUppercase{Dahmen}, W.; \MakeUppercase{Daubechies}, I.; \MakeUppercase{DeVore}, R. Tree approximation and optimal encoding. \textbf{Applied and Computational Harmonic Analysis}, v. 11, n. 2, p. 192--226, 2001. DOI: \refdoi{10.1006/acha.2001.0336}.}`

Fontes anexadas já presentes: DeVore–Popov, Kerkyacharian–Picard, Yang. Não é necessário adicionar entradas para elas.

## 16. Limitações e problemas remanescentes

- **Leituras parciais das quatro fontes.** Li enunciados e demonstrações relevantes ao Teorema 5.2 e à Seção 8, mas não li integralmente as demonstrações dos Teoremas 2 de K–P e 4.6 de Yang, nem as Seções 4–6 de Cohen et al. A comparação de obstrução (seções 4–8) assenta nos enunciados e nas hipóteses, não em um esgotamento das demonstrações.
- **Antecedentes clássicos não lidos:** DeVore–Howard–Micchelli (larguras não lineares) para o piso `N^{-s}`; Binev–DeVore; Whitney/Petrushev; Birman–Solomyak original. Siegel, Elbrächter e Ou et al. por fonte de segunda mão (HTML/ferramenta).
- **Piso `N^{-s}` (E).** Antecedente clássico provável (larguras não lineares) não confirmado.
- **Cor. de DeVore–Popov sobre `A=min(r,r−1+1/p)`:** li a definição e os enunciados; a restrição `α<A` para `r=2` e `p≥1` é inferida do texto. Confiança média.
- **Lei `C²`:** a classe `H<H_R` não está coberta pelo piso aritmético. Elbrächter e Yang tratam `d≥1`; o manuscrito, `d=1`.
- **Bibliografia:** página final de Elbrächter a confirmar; chaves novas a conferir.
- **D (candidato original) não atribuído:** exigiria busca mais ampla que a das fontes prioritárias.

## 17. Parecer científico final

**P1. Os quatro artigos contêm algum teorema equivalente ao Teorema 5.2?** Não. Nenhum possui um parâmetro de altura aritmética e nenhum prova limites bilaterais para aproximação adaptativa por árvores contínuas com racionais de altura limitada. Yang e DeVore–Popov são cotas superiores sem restrição aritmética; Cohen et al. e K–P tratam entropia e codificação. Confiança alta (enunciados lidos).

**P2. A lei bilateral com dois orçamentos independentes permanece contribuição substantiva?** Sim. A lei como um todo não decorre das fontes lidas, e as obstruções são essenciais: entropia ve `H` só por `log H`; inclusão em redes dá cota inferior mais fraca; splines reais não têm restrição de altura. Confiança média-alta.

**P3. Quais partes do Teorema 5.2 vêm de técnicas clássicas e quais exigem argumentos específicos de altura aritmética?** Clássico: o termo superior `N^{-s}` (DeVore–Popov Teor. 4.5), a técnica de grade alternada (Parte II) e, provavelmente, o piso `N^{-s}` (larguras não lineares, a confirmar). Específico: os três pisos de `H` contra árvores adaptativas, a quantização nodal que os realiza e a transição `a(p,s)`. Confiança média.

**P4. A Biblioteca antecipa a lei de Besov ou apenas resultados particulares?** Apenas resultados particulares: a classe `C²` (verificada por reconstrução), o Jackson racional em norma uniforme, a grade alternada, o piso aritmético e a barreira geométrica para malha uniforme. Não antecipa `B^s_{p,q}` em `L^p`, `0<s<2`, os pisos contra árvores adaptativas, a quantização variável nem os regimes críticos. Confiança alta.

**P5. A Seção 8 contém contribuição de informação/codificação ou aplicação de estimativas clássicas?** Aplicação de estimativas clássicas (B), com constantes explícitas e uma conta de bits do catálogo. A observação genuína é que a biblioteca de altura perde um fator `log N` contra a ordem ótima de bits. Não é resultado novo sobre entropia. Confiança alta.

**P6. Os resultados críticos e a quantização variável por nó são contribuições técnicas independentes?** Sim, como extensões técnicas (C): quantização variável por nó, endpoint `p=s=1` por escala, e agenda linear em `s=1/p`. O Teorema 7.1 e a Proposição 7.2 são consequências diretas (B). Confiança média.

**P7. Quais afirmações de originalidade manter, reformular ou retirar?**
- **Manter:** a lei de dois orçamentos para `0<s<2` em `L^p`; pisos válidos contra árvores adaptativas; quantização nodal variável e endpoint `p=s=1` por escala; agenda linear fixa em `s=1/p` como igualdade de conjuntos.
- **Reformular:** o piso geométrico, o `N^{-s}` inferior e a Parte IV como antecedente (distinguir malha uniforme de adaptativa); o expoente `1+1/p` como escalonamento; a Seção 8 como aplicação de resultados clássicos; Elbrächter, Yang e Siegel como analogia, nunca extensão.
- **Retirar:** "primeira lei minimax de Besov com quantização"; "primeiro resultado de aproximação diádica de Besov"; "generalização estrita" de qualquer das fontes; "novo resultado de entropia".

**P8. Existe impedimento científico relevante para E5/E6?** Não. Não foi encontrada falha matemática nos itens verificados, e as lacunas são bibliográficas e delimitadas (seção 16).

**Decisão: B.** E1/E2 estão substancialmente concluídos. Os quatro PDFs foram lidos nos enunciados e provas pertinentes; as reduções foram tentadas e falham por obstruções essenciais; a Parte II foi reconstruída; a lei `C²` foi formalizada; a Seção 8 foi confrontada com K–P e Cohen et al. Ressalvas bibliográficas delimitadas antes da submissão: (i) confirmar o antecedente clássico do piso `N^{-s}` em larguras não lineares; (ii) ler integralmente as demonstrações de K–P Teor. 2 e Cohen et al. Seções 4–6 se a comparação de codificação for aprofundada; (iii) reconfirmar Siegel, Elbrächter e Ou et al. nos PDFs; (iv) completar a página final de Elbrächter e as chaves `lp-cohen2001` e `lp-elbrachter2021`.
