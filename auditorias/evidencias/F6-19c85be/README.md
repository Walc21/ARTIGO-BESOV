# Evidências da auditoria F6

Estes arquivos acompanham o [relatório F6](../../RELATORIO_F6_CERTIFICACAO_FINAL.md) da auditoria de
[19c85be8bd08098b4a8c6d0452e755b5e3683be7](https://github.com/Walc21/ARTIGO-BESOV/commit/19c85be8bd08098b4a8c6d0452e755b5e3683be7).
As saídas e os scripts têm os bytes da execução citada no relatório. O
[manifesto do Lake](lake-manifest.json) é uma cópia do arquivo versionado no SHA auditado e fixa
as nove dependências. Os resultados deste diretório são históricos.

- [Compilação principal](build.log), [alvos complementares](build-completo.log),
  [download do cache](cache.log) e [inventário de objetos do projeto antes do build](projeto-olean-antes.log).
  O inventário vazio registra a ausência inicial de arquivos `.olean` do projeto.
- [Consultas de axiomas](axiomas-auditoria.log), [extrator de dependências](DeclaracoesF6.lean),
  [testes semânticos](SemanticaF6.lean) e [saída semântica](semantica.log).
- [Imports locais](imports.tsv), [declarações](declaracoes.tsv), [arestas](arestas.tsv),
  [módulos](modulos.tsv), [resumo do grafo](grafo.log) e [códigos de saída](status.tsv).
  O teste Lean de regressão terminou com código 0 e saída vazia, preservada em [minimax52.log](minimax52.log).
- [Regressão Python](unittest.log) e [verificação do mapa](mapa.log).
  As saídas antecipadas citadas no relatório também foram preservadas.

Valide as cópias com `sha256sum -c SHA256SUMS` neste diretório. O SHA-256 do relatório original
era `29734f177011100fa8c0042b8894ea16f1bece6cfce665e1c30772687717f395`.
O SHA-256 da edição com links portáveis é `3f2f3ddd644098a085dad6fcb77d0a5b7044b7ecc17d93df8b51eec99d569b43`.
A publicação ajusta os destinos dos links. As referências de linha apontam para o commit auditado.

Para reproduzir os comandos da seção 2 do relatório, use uma cópia limpa no SHA auditado,
com a versão do Lean e as dependências fixadas no manifesto. Copie este diretório para um local
gravável e execute ali `bash ReproduzirF6.sh /caminho/do/checkout-certificado`. O script grava
novos logs ao lado da cópia. Para regenerar as tabelas do grafo nessa mesma cópia, execute
`python3 -B resumir_grafo.py declaracoes.log`.

O diretório de downloads do cache e a árvore de compilação ficaram na execução local.
Os arquivos exploratórios `PreviaGrafo.lean` e `PreviaSemantica.lean` deram lugar aos dois testes Lean citados no relatório.
