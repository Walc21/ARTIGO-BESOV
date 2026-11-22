"""Extrai a parte local do fechamento a partir de DeclaracoesF6.lean."""

from collections import Counter
from pathlib import Path
import sys

directory = Path(__file__).resolve().parent
graph_records = {label: [] for label in ('F6TOTAL', 'F6NODE', 'F6EDGE')}

log = Path(sys.argv[1]) if len(sys.argv) > 1 else directory / 'declaracoes.log'
for line in log.read_text().splitlines():
    for label, records in graph_records.items():
        if label + '\t' in line:
            records.append(tuple(line.split(label + '\t', 1)[1].split('\t')))
            break

(totals,) = graph_records['F6TOTAL']
central_total, central_local, union_total, union_local = map(int, totals)
nodes = {name: (module, central, kind) for name, module, central, kind in graph_records['F6NODE']}
edges = sorted(set(graph_records['F6EDGE']))
assert len(nodes) == union_local
assert all(name in nodes and dependency in nodes for name, dependency, _, _ in edges)
assert sum(central == 'yes' for _, central, _ in nodes.values()) == central_local

def tsv(name, header, rows):
    (directory / name).write_text(header + '\n' + ''.join('\t'.join(row) + '\n' for row in rows))

tsv('declaracoes.tsv', 'nome\tmodulo\tno_teorema\ttipo',
    [(name, *fields) for name, fields in sorted(nodes.items())])
tsv('arestas.tsv', 'origem\tdestino\tmodulo_origem\tmodulo_destino', edges)
central_edges = [edge for edge in edges if nodes[edge[0]][1] == nodes[edge[1]][1] == 'yes']
modules = Counter(module for module, central, _ in nodes.values() if central == 'yes')
tsv('modulos.tsv', 'modulo\tdeclaracoes_no_teorema',
    [(module, str(count)) for module, count in sorted(modules.items())])
print(f'teorema={central_total}, locais={central_local}, modulos={len(modules)}, arestas_locais={len(central_edges)}')
print(f'uniao={union_total}, locais={union_local}, arestas_locais={len(edges)}')
print('módulos por biblioteca:', Counter(module.split('.')[0] for module in modules))
print('axiomas ou declarações opaque do projeto:',
      [name for name, (_, _, kind) in nodes.items() if kind in {'axiom', 'opaque'}])
print('declarações de escopo investigadas no fechamento:',
      [name for name in nodes if name.endswith(('.HypJp', '.HypJpStrong', '.jointErr', '.critical_lq',
                                             '.critical_level', '.critical_rate'))])
