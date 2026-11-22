# Relatório E5/E6 — consolidação editorial, bibliográfica e técnica

Esta etapa não refaz a integração E1/E2 e não inclui a formalização integral do Teorema 5.2 em Lean 4. O projeto **não é declarado pronto para submissão**: isso depende da etapa posterior de formalização e da validação científica final.

## 1. Estado inicial do repositório

- Branch `pesquisa-minimax-altura`, commit de referência `eb8af0d29b9a9d07ead011342f7e763fef04669e`, árvore limpa. Commit anterior (integração E1/E2): `bf530161744467b9ae70b1ea5220e7c268f70424`.
- Procedimento oficial lido no `README.md`: compilar com `latexmk`, compilar o Lean (`lake build Formalizacao`), buscar `sorry`, auditar axiomas, rodar `mapas/verificar_mapa.py` e `python3 -B -m unittest discover -s testes -v`.
- Dependências identificadas: a edição ABNT carrega `conjecturas_lp.tex` por `\input`; as três edições compartilham `conjecturas_lp_estilo.sty`, `conjecturas_lp_citacoes.tex` e `conjecturas_lp_referencias.tex`; `mapas/MAPA_TEX_LEAN.md` é gerado a partir dos rótulos de `conjecturas_lp.tex` (números de linha) e dos nomes Lean; `testes/test_edicoes.py` confere rótulos, referências e citações entre as três edições.
- Documentos consultados: os relatórios E1/E2 e de integração (produzidos nas etapas anteriores desta sessão); o relatório E3/E4, para as âncoras de linha; `RELATORIO_VALIDACAO_ETAPA_2.md`, `RELATORIO_VALIDACAO_INTEGRACAO.md`, `AUDITORIA_INTEGRACAO.md` e `mapas/AUDITORIA_FIDELIDADE.md` apenas por contagem de âncoras e para delimitar o escopo, sem releitura integral. Do manuscrito foram lidos diretamente o resumo, a introdução, as aberturas de seção, a Seção 8, as considerações finais e a Seção de Lean.

## 2. Arquivos modificados

| Arquivo | Alteração |
|---|---|
| `conjecturas_lp.tex` | Resumo; três parágrafos de abertura de seção; nova `lp:obs:c2-joint`; frase da introdução sobre a lei `C²`. |
| `conjecturas_lp_en.tex` | As mesmas alterações, em inglês. |
| `conjecturas_lp_referencias.tex` | Entradas de Elbrächter et al. (DOI) e Birman–Solomyak (tradução e DOI). |
| `mapas/MAPA_TEX_LEAN.md` | Regenerado pelo gerador oficial (somente números de linha). |
| `RELATORIO_CORRECOES_E3_E4.md` | 12 âncoras de linha atualizadas (conteúdo inalterado). |
| `README.md` | Linha de `auditorias/` na tabela; nota sobre `sorry` corrigida. |
| `conjecturas_lp.pdf`, `conjecturas_lp_en.pdf`, `conjecturas_lp_abnt.pdf` | Regenerados. |
| `auditorias/PENDENCIAS_REVISAO_FINAL.md` | Seção de atualização acrescentada; histórico preservado. |
| `auditorias/RELATORIO_E5_E6_CONSOLIDACAO.md` | Este relatório. |

Não foram alterados: `conjecturas_lp_abnt.tex`, `conjecturas_lp_estilo.sty`, `conjecturas_lp_citacoes.tex`, testes, scripts, nada em `lean4/` e os relatórios de auditoria E1/E2.

## 3. Correções editoriais e bibliográficas

**Resumo (PT e EN).** Acrescentadas duas frases: (a) a caracterização global em `p=s=1` com `q<∞` sob agenda linear permanece em aberto; (b) o alcance da formalização em Lean 4. A (b) foi escrita a partir da própria Seção de Lean do artigo: a formalização cobre a caracterização por realização, a estabilidade em redes, as cotas uniformes e o piso aritmético; a lei minimax, o quantizador por nó, a agenda linear fixa e o crescimento no raio são demonstrados no artigo e ainda não foram certificados em Lean.

**Transições.** As Seções 3, 6 e 7 começavam diretamente por um teorema. Receberam um parágrafo de abertura de duas frases que descreve o que a seção faz, em PT e EN. Nenhuma afirmação matemática nova.

**Bibliografia.**

| Entrada | Verificação | Resultado |
|---|---|---|
| Elbrächter et al. | Crossref | IEEE TIT 67(5), p. 2581–2623, 2021, DOI `10.1109/TIT.2021.3062161`. DOI incluído. |
| Birman–Solomyak | Crossref | *Math. USSR-Sbornik* 2(3), p. 295–317, 1967, DOI `10.1070/SM1967v002n03ABEH002343`. Entrada corrigida para citar a tradução inglesa. Original russo não confirmado. |
| Cohen et al. | Crossref e cabeçalho do PDF | ACHA 11(2), p. 192–226, 2001, DOI `10.1006/acha.2001.0336`. Conforme. |
| Kerkyacharian–Picard | Crossref | ESAIM P&S 7, p. 239–250, 2003, DOI `10.1051/ps:2003011`; sem fascículo. Conforme. |
| DeVore–Popov (1988a) | Crossref | TAMS 305(1), p. 397–414, DOI `10.1090/S0002-9947-1988-0920166-3`. Conforme. |
| Siegel | Página do JMLR | JMLR 24(357), p. 1–52, 2023. Conforme. |
| Yang | arXiv:2409.00901 | Entrada preexistente, sem alteração. |
| Biblioteca Determinística | — | Entrada `lp-oliveiravol`, volume do autor; ver pendências. |

Coerência entre os dois arquivos: 22 entradas de referência, 22 de citação, 22 chaves citadas, nenhuma órfã nem indefinida.

## 4. Ajustes da lei `C²`

A atribuição anterior ("decorre" da Parte II) dependia de uma dedução registrada apenas no relatório E1/E2. Foi acrescentada a `lp:obs:c2-joint` (Seção 5, após `lp:obs:floor-closure`, de modo que nenhum resultado numerado muda de número). Ela:

1. atribui à Parte II só o que ela demonstra: para `n=2^r≥2`, montagem de `n` folhas, erro `≤(M+4)/(8n²)` e altura `≤C_Hn²` na classe `F_{R,M}`;
2. deduz a cota superior para `(N,H)` independentes (escolha de `n` como a maior potência de dois com `n≤min{N,√(H/C_H)}`, e o segmento afim `(x−1/2)/H` para `H<4C_H`);
3. deduz a cota inferior por `f=λx²`, `λ=min{R,M/2}` (folha de comprimento `≥1/N` e erro uniforme `λℓ²/8`), e pelo piso aritmético com a constante `1/(2H)` para `H≥1/(2R)`;
4. declara que a lei é consequência de resultados anteriores e não é o caso `s=2` do Teorema 5.2, cuja hipótese é `0<s<2`.

A frase da introdução foi reescrita para apontar para essa observação e deixar de atribuir à Parte II a lei bilateral.

A dedução foi verificada independentemente na rodada E1/E2 (reconstrução da demonstração da Parte II e do piso quadrático; ver `RELATORIO_E1_E2_CONCLUSIVO_4_FONTES.md`, seções 10 e 11). A cota superior da observação depende do enunciado da Parte II, que o leitor encontra em `lp-oliveiravol`.

## 5. Equivalência PT/EN

- `test_rotulos_unicos_e_na_mesma_ordem` e `test_referencias_e_citacoes_resolvidas` passam: mesmos rótulos, na mesma ordem, e referências e citações resolvidas nas três edições.
- O novo rótulo `lp:obs:c2-joint` existe nas duas línguas. Todas as passagens novas (resumo, aberturas, observação, introdução) foram escritas em pares com as mesmas fórmulas, chaves de citação e referências cruzadas.
- Numeração: comparação dos arquivos `.aux` de `eb8af0d` e do estado atual, nas três edições. Dos 117 rótulos preexistentes, nenhum mudou de número; há 1 rótulo novo.
- Correspondência de resultados confirmada pelos 109 blocos matemáticos idênticos em PT e EN (seção 11).
- Revisão ortográfica: em inglês, `aspell` apontou apenas termos técnicos. **Em português não foi possível**: o dicionário `pt_BR` do `aspell` não está instalado.

## 6. Compilação dos PDFs

Gerados com `latexmk -pdf -interaction=nonstopmode -halt-on-error conjecturas_lp.tex conjecturas_lp_abnt.tex conjecturas_lp_en.tex` (código 0).

| PDF | Páginas | Tamanho | Fontes | Observações |
|---|---|---|---|---|
| `conjecturas_lp.pdf` | 31 | 595 602 B | 27, todas incorporadas | sem erros, sem referência indefinida, sem `Overfull`, `Underfull` ou aviso de pacote |
| `conjecturas_lp_en.pdf` | 32 | 560 357 B | 24, todas incorporadas | idem |
| `conjecturas_lp_abnt.pdf` | 34 | 568 028 B | 22, todas incorporadas | idem |

Exame além da compilação: metadados PDF (título, assunto, palavras-chave e autor corretos nas três edições; A4); nenhuma página com menos de 200 caracteres de texto extraível; nenhum `??` no texto extraído; renderização e leitura visual da primeira página das três edições, da página da nova observação (PT e EN) e da página de referências (ABNT). Equações, observação, resumo e referências aparecem corretos. **Não foi feita uma leitura visual de todas as páginas**; as demais foram verificadas apenas por extração de texto e pelos logs.

## 7. Testes

- `python3 -B -m unittest discover -s testes -v`: 9 testes, todos OK.
- `python3 mapas/verificar_mapa.py`: 64 entradas, 263 nomes Lean localizados, todos aceitos pelo Lean (`#check`), `MAPA_TEX_LEAN.md` atualizado. Antes da regeneração, o verificador acusou o mapa como desatualizado, como esperado (as aberturas de seção deslocaram linhas). O mapa foi regenerado pelo gerador oficial (`python3 mapas/gerar_mapa.py`), sem preservar artificialmente o número de linhas. A diferença no mapa são 57 linhas, todas idênticas após normalizar o número de linha do TeX.
- Âncoras de linha de `RELATORIO_CORRECOES_E3_E4.md`: 12 atualizadas por mapeamento exato entre as versões; as 6 entradas com rótulo conferidas contra os arquivos novos.

## 8. Verificação Lean

Ambiente: Lean 4.28.0. Nenhum arquivo em `lean4/` foi modificado (`git status` vazio para o diretório).

| Verificação | Resultado |
|---|---|
| (1) Compilação dos módulos | `lake build Formalizacao`: `Build completed successfully (8133 jobs)`. Há um aviso de variável não usada (`hp`) em `AlturaCritical3.lean:276`, preexistente. |
| (2) Aceitação dos nomes pelo kernel | `verificar_mapa.py`: o Lean aceitou os 263 nomes por `#check`. |
| Axiomas | `lake env lean Formalizacao/Auditoria.lean`: 201 linhas, `diff` contra `auditoria_axiomas.txt` vazio (código 0). Todas as linhas registram apenas `propext`, `Classical.choice` e `Quot.sound`; nenhuma ocorrência de `sorryAx`. |
| Busca por `sorry` | `grep -rnw 'sorry' Formalizacao/ Formalizacao.lean`: **1 ocorrência**, em `Formalizacao/AlturaBump.lean:13`, dentro de um docstring (`nenhum resultado depende de \`sorry\``). Não é uma lacuna de prova. O README dizia que a saída esperada era vazia; a nota foi corrigida. |
| (3) Fidelidade dos enunciados ao LaTeX | **Não foi reexecutada nesta etapa.** Permanece o que consta em `mapas/AUDITORIA_FIDELIDADE.md`, que não foi alterado. A compilação e o `#check` não provam fidelidade. |
| (4) Cobertura | **Parcial.** Conforme o README e a Seção de Lean do artigo: formalizados a caracterização por realização, a estabilidade em redes (inclusão exata e aproximada), as cotas uniformes, o piso aritmético, os pisos geométrico e por inclinação, a necessidade conjunta, a altura crítica por bola para `q` finito, as descrições binárias e as agendas de log iterado. **O Teorema 5.2 (lei minimax), o quantizador por nó, a extensão crítica a `q=∞`, a agenda linear fixa e o crescimento ótimo no raio não estão certificados em Lean**, e o resumo agora diz isso. |

Nenhuma dependência Lean foi removida ou substituída, nenhum axioma novo foi introduzido e nenhum `sorry` novo foi adicionado.

## 9. Pendências remanescentes

1. **Metadados da edição ABNT em branco**, não inventados: `\besovcontact`, `\besovsubmitted`, `\besovaccepted`, `\besovabntedition` (em `conjecturas_lp_abnt.tex`). Instituição e vínculo acadêmico não constam (o texto traz "Pesquisador independente"). Não há DOI do manuscrito.
2. **Convenção de maiúsculas nas citações parentéticas da edição ABNT.** O estilo do projeto escreve "(Birman; Solomyak, 1967)". Se a NBR 10520:2023 exigir caixa alta nas citações entre parênteses, isso se aplica a todas as entradas, e não só às novas. **O texto da norma não foi consultado**, então não é possível afirmar se é requisito normativo ou escolha de estilo.
3. **Birman–Solomyak.** Citada a tradução inglesa verificada. O original (*Mat. Sb.* 73) não foi confirmado.
4. **`lp-oliveiravol`** (Biblioteca Determinística, Partes II e IV) é um volume do autor; o leitor externo precisa de acesso a ele para conferir a Parte II, de que a `lp:obs:c2-joint` depende.
5. **Revisão ortográfica em português** não realizada (sem dicionário).
6. **Profundidade da revisão editorial.** Foram revisados com leitura direta: resumos, palavras-chave, introdução, aberturas de seção, Seção 8, considerações finais e Seção de Lean. As demonstrações das Seções 2–7 e os apêndices não foram relidos linha a linha nesta etapa, e sim cobertos por verificações mecânicas (rótulos, referências, citações, blocos matemáticos idênticos) e pelas auditorias E3/E4 e E1/E2.
7. **Lean:** fidelidade dos enunciados não reexecutada nesta etapa; o aviso de variável não usada em `AlturaCritical3.lean` é preexistente.
8. **Antecedentes ainda não lidos integralmente** (auditoria E1/E2, seção 16): larguras não lineares (DeVore–Howard–Micchelli) para o piso `N^{-s}`, demonstrações completas de Kerkyacharian–Picard e Cohen et al., releitura de Siegel, Elbrächter e Ou et al. nos PDFs.
9. **Nenhum erro matemático novo foi encontrado** nas passagens revisadas.

## 10. Limitações da formalização

O Teorema 5.2 (lei minimax em dois orçamentos), o quantizador por nó, a extensão crítica a `q=∞`, a agenda linear fixa e o crescimento ótimo no raio têm demonstração analítica no artigo e **não** estão certificados em Lean; a Seção de Lean do artigo, o README e o resumo dizem isso. A formalização existente usa representantes mensuráveis `ℝ→ℝ`, constantes de Jackson que podem depender de `f` em vários módulos, e parte dos casos assume `1/p<s<2`. A formalização integral do Teorema 5.2 será realizada em etapa separada. O projeto não deve ser descrito como integralmente formalizado.

## 11. Diff resumido e justificativas

```
 README.md                      |   3 +-
 RELATORIO_CORRECOES_E3_E4.md   |  12 ++---
 conjecturas_lp.tex             |  19 ++++++-
 conjecturas_lp_en.tex          |  19 ++++++-
 conjecturas_lp_referencias.tex |   4 +-
 mapas/MAPA_TEX_LEAN.md         | 114 ++++++++++++++++++++---------------------
 conjecturas_lp.pdf, conjecturas_lp_en.pdf, conjecturas_lp_abnt.pdf (binários, regenerados)
 auditorias/PENDENCIAS_REVISAO_FINAL.md, auditorias/RELATORIO_E5_E6_CONSOLIDACAO.md
```

**Regressão matemática, comparada com `eb8af0d`.** Nas duas edições, os 109 blocos matemáticos (teorema, lema, proposição, corolário, definição, demonstração, equações, enumerações e tabelas Lean) e as 81 fórmulas em display são idênticos, excluindo apenas o texto das observações (onde está a observação nova). Nenhum enunciado, hipótese, constante, fórmula ou demonstração foi alterado. Todos os 117 rótulos preexistentes mantêm o número, e há 1 rótulo novo (`lp:obs:c2-joint`).

**Alterações relevantes e justificativas.**

| Alteração | Justificativa |
|---|---|
| Resumo: limitação da caracterização global e alcance da formalização | O resumo deve representar os resultados demonstrados e o alcance da certificação Lean, sem sugerir formalização integral. |
| Aberturas das Seções 3, 6, 7 | Seções que começavam por um teorema; apenas descrevem o conteúdo existente. |
| `lp:obs:c2-joint` e frase da introdução | Torna a lei `C²` verificável no próprio artigo e a atribui corretamente. Fica em `Observação`, após a última observação da Seção 5, sem deslocar a numeração. |
| Entradas de Elbrächter et al. e Birman–Solomyak | Metadados confirmados em Crossref; evita citar páginas da tradução como se fossem do original. |
| Mapa regenerado | As aberturas deslocaram linhas; o gerador oficial é a fonte do mapa. Só os números de linha mudam. |
| README | A busca por `sorry` não retorna vazio por causa de um docstring; a nota foi corrigida; a pasta `auditorias/` foi listada. |
| Âncoras de linha em `RELATORIO_CORRECOES_E3_E4.md` | Os links apontavam para linhas deslocadas; atualização mecânica, sem mudar o texto. |

Nenhuma outra edição de redação foi feita. Em particular, não houve refatoração, reformulação estilística de demonstrações nem alteração de fórmulas por razões de estilo.
