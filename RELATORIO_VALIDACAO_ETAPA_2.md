# ARTIGO-BESOV · Validação da Etapa 2

21 de novembro de 2026

## I. Estado Git

Branch `pesquisa-minimax-altura`. Base e HEAD inicial `36192a75fc8c0b4f26e4690c5778357a8aea4874`, com árvore de trabalho inicialmente limpa.

| Commit local | Conteúdo |
|---|---|
| `c1aa201f4b23acc21ff7eecf899856d7c89c9ae3` | Revisão das provas, nove blocos, aplicação em \(p=s=1\) e testes exatos. Os fundamentos, o minimax e a altura crítica entraram juntos porque a prova minimax usa as duas construções críticas. |
| `04897a03c36267f9559d4454ce1abdb3bd81b289` | Estrutura, título, resumos e introduções PT/EN, fontes e três PDFs, teste de integridade editorial. |
| Commit que contém este relatório | README, dados e versão gerada do mapa TeX–Lean, auditoria de fidelidade e registro de validação. |

O SHA do commit documental pode ser obtido com `git log -1 --format=%H -- RELATORIO_VALIDACAO_ETAPA_2.md`. A comparação completa de arquivos está em `git diff --name-status 36192a75 HEAD`. A Biblioteca Unificada foi consultada localmente em `3854ac7125a599e4901e38338409749e9ead94b9`, branch `lacunas-restantes`. O estado observado antes e depois inclui a modificação preexistente em `.gitignore`. A integração e os commits são locais.

## II. Integração

O Teorema 5.2 passou a ser o resultado principal. A seção correspondente vem após as ferramentas de construção e os pisos. O Corolário 5.4 transfere a ordem minimax para a realização. A seção 6 retém os enunciados e as provas da caracterização geral e da estabilidade de redes. A seção 7 desenvolve a agenda fixa, seu controle quantitativo e as agendas de log iterado. A seção 8 reúne codificação e entropia. Os 105 rótulos explícitos da base estão presentes, além de nove novos. A comparação por blocos encontrou 49 enunciados rotulados na base, todos preservados, dos quais seis receberam os ajustes relacionados à Etapa 2. O número de provas passou de 41 para 48 em cada língua.

## III. Matriz dos nove blocos

| Bloco | Rótulo | Estado | Verificação | Limitação |
|---|---|---|---|---|
| Piso geométrico | `lp:prop:geom-floor` | Integrado | Endereço da folha terminal e teste contra afins, inclusive para o zero | O calibre inclui o endereço |
| Constante de Nikolskii | `lp:eq:nikolskii` | Integrada | Reprodução pelo projetor e cotas nos extremos | A desigualdade usa afinidade na célula |
| Piso de folhas | `lp:lem:leaf-budget-floor` | Integrado | \(2N\) bumps, no máximo \(N-1\) fronteiras e teste por \(\varphi''\) | Prova analítica |
| Lei minimax | `lp:thm:minimax-nh` | Integrada | Pisos, construção por regime, arredondamento diádico e zero | Prova analítica |
| Quantização por nó | `lp:lem:nodal-variable-height` | Integrada | Prova aritmética e 609 conjuntos nodais admissíveis em frações exatas | A estimativa é em \(L^1\) |
| Minimax da realização | `lp:cor:minimax-realization` | Integrado | Comparação por escala e módulo de Besov para todo \(N\) inteiro | A equivalência minimax é analítica |
| Altura crítica | `lp:thm:critical-linear` | Estendida | Três condições de altura e sequência geométrica com fator polinomial | A extensão de sequência a \(q=\infty\) é analítica |
| Agenda linear fixa | `lp:thm:critical-fixed-agenda` | Integrada | Inclusão de orçamentos, monotonicidade do módulo e bloco inicial | Enunciado principal com \(p>1\) |
| Crescimento no raio | `lp:prop:critical-radius-growth` | Integrado | Cota via deslocamento mínimo e cota por alvos constantes | Ordem ótima para raios grandes |

## IV. Revisão matemática

Para um nó com peso \(w_j=1+J+|y_j|\), a maior potência de dois \(Q_j\le H/(8w_j)\) é positiva. Em cada nó ímpar, entre o ponto da grade mais próximo e seus dois vizinhos, ao menos um difere dos valores dos dois nós pares já quantizados. A construção preserva a continuidade e torna todas as inclinações não nulas. Em cada folha, \(D=\max(Q_j,Q_{j+1})\) é divisível pelos dois denominadores e \(D\le H/(8\min(w_j,w_{j+1}))\). O salto limitado permite usar esse peso mínimo para controlar as duas amplitudes. Se \(D\ge n\), cancela-se o fator diádico da malha na inclinação. Se \(D<n\), a inclinação é inteira e limitada por \(n(J+4)\). A integral do módulo do erro afim é limitada pela média dos erros nos extremos multiplicada pelo comprimento da folha.

Em \(p=s=1\), a prova de saltos usa apenas \(p\ge1\) e o controle dos coeficientes do módulo. A projeção local dá \(|\lambda_j|\le4n\|f\|_{L^1(I_{c(j)})}\). A célula final é usada duas vezes, portanto a média dos módulos nodais é no máximo \(8\|f\|_1\). Com \(H\ge C(B+1)n\), a quantização contribui com \(O((B+1)/H)\), sem logaritmo. Essa parte integra a Proposição 3.19.

## V. Resultados minimax

Para \(1\le p<\infty\), \(0<s<2\) e \(0<q\le\infty\), a ordem é \(N^{-s}+H^{-s/a(p,s)}\), com constantes dependentes apenas de \(p,s,q\). Para a taxa \(N^{-s}\), a potência ótima de altura é \(a=1+1/p-s\) abaixo de \(1/p\), \(a=1\) de \(1/p\) a \(1\) e \(a=s\) acima de \(1\).

| Caso revisto | Passo que o cobre |
|---|---|
| \(p=1\) | Hölder com conjugado infinito no piso de folhas e estimativa integral no endpoint |
| \(q<1\), \(q=1\), \(q=\infty\) | Soma das potências \(q\) ou supremo no empacotamento. O caso \(p=s=1\) usa a mesma cota superior por escala para todo \(q\). |
| Diagonal e \(s=1\) | Piso geométrico na faixa intermediária. A construção crítica cobre a diagonal, e acima dela o denominador \(Q=n\) funciona até \(s=1\). |
| \(N=H=2\) | O zero cobre limiares pequenos. Os pisos e a contagem de fronteiras continuam válidos. |
| \(N\gg H\) e \(H\gg N^a\) | O menor dos dois limites determina o nível diádico da construção. A cota inferior vale para todos os pares. |
| Árvores adaptativas | A contagem de fronteiras e o argumento da folha terminal valem para cada representação admissível. |
| Alvo fixo | Os testes inferiores podem variar com o orçamento. Por exemplo, a função \(x\) é representável com altura 2. |

## VI. Altura crítica

A agenda \(H_B\) estende o teorema por bola a \(q=\infty\). O termo normalizado de quantização é limitado por \(C(r+2)2^{-r(1-1/p)}\), pois o fator \(B+1\) é absorvido pela altura. A agenda fixa com qualquer prefator positivo usa deslocamento dependente do raio, e a inclusão inversa é universal. O crescimento \(B^{1+1/p}\) resulta de uma cota superior para a sequência inteira e de um orçamento diádico de ordem \(K\) para o alvo constante \(K\). Isso distingue igualdade de conjuntos, uniformidade por bola e a equivalência linear uniforme, que é falsa. Em \(p=s=1, q=\infty\), o mesmo deslocamento funciona para o supremo.

## VII. Parte IV da Biblioteca Unificada

A Parte IV, em `tex/partes/artigo_3.tex`, já contém a biblioteca (linhas 18–42), Jackson racional e a quantização por denominador comum (277–382), um piso aritmético (555–581), o funcional de realização (1289–1419) e o deslocamento diádico para redes (1466–1527). A integração aproveita a comensurabilidade de denominadores e o deslocamento. O minimax em dois orçamentos, a média nodal no endpoint \(L^1\) e o crescimento ótimo no raio para a agenda crítica em \(L^p\) são as extensões deste artigo. Essa comparação documenta a anterioridade interna. A ordem de prioridade na literatura externa permanece indeterminada.

## VIII. Sincronização das edições

PT e EN têm os mesmos 114 rótulos explícitos, na mesma ordem, mais os três rótulos gerados por quadros compartilhados. A ABNT importa a fonte PT, inclusive os resumos. As três edições carregam o estilo, as chaves de citação e a bibliografia compartilhados, conforme os arquivos do gravador do LaTeX. A tabela de agendas distingue a taxa por escala da somabilidade. A edição PT usa referências em tamanho reduzido para manter a bibliografia na última página. A edição EN mantém o enunciado principal e a expressão de \(a(p,s)\) na mesma página. As referências bibliográficas já continham os antecedentes citados na nova introdução.

## IX. Testes e reprodução

- `python3 -B -m unittest discover -s testes -v` passou os sete métodos de teste. São 600 conjuntos aleatórios com semente 63, nove conjuntos adversariais admissíveis, um caso abaixo do limiar e quatro verificações editoriais. Os conjuntos cobrem \(D<n\), \(D=n\), \(D>n\), mudanças de grade entre nós, dados constantes e quase constantes e alturas no limiar.
- `python3 -B mapas/gerar_mapa.py --verificar` e `python3 -B mapas/verificar_mapa.py` confirmam o mapa gerado, 64 entradas e 263 referências a nomes Lean, com 244 nomes distintos.
- `latexmk` 4.88 e pdfTeX 1.40.29 compilaram os três PDFs. Os logs finais ficaram sem avisos, referências ou citações indefinidas e caixas excedentes. As três saídas passaram em `qpdf --check`. A inspeção dos arquivos auxiliares encontrou 117 rótulos distintos por edição. O pypdf verificou 798 links internos com destino nomeado. A inspeção visual revisou as 90 páginas em folhas de contato e páginas centrais em maior resolução.
- `git diff --check` passou. Os PDFs entregues são cópias byte a byte das saídas verificadas.

Para regenerar os PDFs a partir da raiz:

```bash
saida=$(mktemp -d)
export SOURCE_DATE_EPOCH=$(date -d '2026-11-21 00:00:00 -03:00' +%s)
export FORCE_SOURCE_DATE=1
latexmk -pdf -recorder -interaction=nonstopmode -halt-on-error -file-line-error \
  -outdir="$saida" conjecturas_lp.tex conjecturas_lp_en.tex conjecturas_lp_abnt.tex
for pdf in "$saida"/*.pdf; do
  qpdf --check "$pdf"
done
```

Os testes aritméticos verificam instâncias da construção. As estimativas gerais decorrem das provas do manuscrito.

## X. Lean 4

Na raiz do projeto Lean, `lake build Formalizacao RequestProject Pendencias` passou com 8.189 tarefas, incluindo 49 recompilações observadas e reutilização de cache nas demais. O log contém avisos de lint em módulos preexistentes. A consulta separada `lake env lean Formalizacao/Auditoria.lean` terminou com 201 consultas sobre 196 declarações distintas e resultados idênticos ao registro versionado. Os únicos axiomas foram `propext`, `Classical.choice` e `Quot.sound`. A busca por `sorry` encontrou zero ocorrências nos 162 arquivos examinados.

O [mapa](mapas/MAPA_TEX_LEAN.md) e a [auditoria de fidelidade](mapas/AUDITORIA_FIDELIDADE.md) distinguem enunciados cobertos e lemas de apoio. As declarações críticas por nível usam diretamente cotas do módulo. As declarações de sequência para \(H_B\) exigem \(q\) finito. Os novos teoremas minimax, o lema por nó, a extensão sequencial a \(q=\infty\), a agenda fixa e o crescimento do raio são analíticos.

## XI. Arquivos finais

| Edição | PDF | Fonte | Páginas |
|---|---|---|---:|
| Português | [PDF](conjecturas_lp.pdf) | [TeX](conjecturas_lp.tex) | 29 |
| Inglês | [PDF](conjecturas_lp_en.pdf) | [TeX](conjecturas_lp_en.tex) | 29 |
| ABNT | [PDF](conjecturas_lp_abnt.pdf) | [TeX](conjecturas_lp_abnt.tex) | 32 |

## XII. Pendências para submissão

- **Matemática.** A caracterização com agenda linear em \(B^1_{1,q}\) para \(q<\infty\) permanece em aberto. Ela está fora do enunciado minimax demonstrado.
- **Editorial.** A edição ABNT tem campos de contato, submissão e aprovação a preencher com os dados confirmados. A revisão científica final deve considerar os novos enunciados e as alegações de contribuição.
- **Bibliográfica.** A prioridade externa da lei minimax e da quantização por nó requer verificação específica antes de qualquer alegação de prioridade.

## XIII. Parecer

Os nove blocos estão integrados. O lema de quantização foi revalidado analiticamente e testado em frações exatas, e a taxa no endpoint \(p=s=1\) é livre da perda logarítmica. As duas cotas minimax estão demonstradas. A extensão crítica a \(q=\infty\), a agenda fixa e a obstrução à equivalência linear uniforme constam no texto. Os três PDFs foram compilados e os testes executados passaram. O manuscrito está pronto para revisão científica final.
