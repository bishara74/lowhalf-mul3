"""Check reference integrity and the manually audited proof dependencies."""

import re
from collections import Counter
from hashlib import sha256
from pathlib import Path


DEPENDENCIES = {
    'thm:MC': ('sec:upper', 'l4:lem:normal', 'thm:lambda5', 'l4:thm:main',
               'l3:thm:main', 'l2:thm:main', 'l1:thm:main'),
    'l4:thm:main': ('l4:lem:Qonly', 'l4:lem:cross', 'l4:lem:types', 'l4:lem:support',
                    'l4:lem:deriv', 'l4:prop:B'),
    'l4:prop:B': ('l4:lem:cross', 'l4:lem:planeU', 'l4:lem:noq2'),
    'l3:thm:L4': ('l4:thm:main',),
    'l3:lem:P': ('l3:lem:rad', 'l3:lem:wt'),
    'l3:lem:A': ('l3:lem:P',),
    'l3:lem:D1': ('l4:lem:types',),
    'l3:lem:C': ('l3:lem:deriv', 'l3:lem:D1', 'l4:thm:main', 'l4:lem:planeU', 'l4:lem:noq2'),
    'l3:prop:B': ('l3:lem:A', 'l3:lem:abs', 'l3:thm:L4'),
    'l3:lem:B3U': ('l4:lem:support',),
    'l3:prop:B3': ('l3:lem:B3U', 'l3:lem:C', 'toolkit:coset'),
    'l3:thm:main': ('l4:lem:normal', 'l4:lem:Qonly', 'l3:lem:C', 'l3:prop:B', 'l3:prop:B3'),
    'l2:lem:replace': ('l3:lem:P', 'l4:lem:Qonly'),
    'l2:lem:lastfactor': ('l4:lem:types', 'l4:lem:support'),
    'l2:lem:coset': ('toolkit:coset',),
    'l2:prop:onehigh': ('l2:lem:coset', 'l2:lem:rankext', 'l2:lem:lastfactor', 'l2:lem:ideal'),
    'l2:thm:main': ('l2:lem:replace', 'l3:thm:main', 'l2:prop:onehigh'),
    'l1:lem:reduce': ('l2:lem:replace', 'l3:lem:P', 'l4:lem:Qonly', 'l2:thm:main'),
    'l1:lem:first': ('l1:lem:cubic', 'l3:lem:P'),
    'l2:lem:four': ('l4:lem:support', 'l3:lem:P', 'l3:lem:rad', 'l3:lem:wt'),
    'l1:lem:corecoset': ('l1:lem:cubic', 'toolkit:coset'),
    'l1:lem:earlycore': ('l1:lem:cubic', 'l4:lem:support', 'l2:lem:four'),
    'l1:prop:corebranch': ('l1:lem:corecoset',),
    'l1:lem:ordinarypair': ('l1:lem:cubic', 'l1:lem:corecoset', 'toolkit:coset'),
    'l1:lem:noncoremult': ('l1:lem:cubic', 'l1:lem:ordinarypair'),
    'l1:lem:noncore': ('l1:lem:ordinarypair', 'l1:lem:noncoremult', 'l2:lem:ideal', 'l2:lem:rankext'),
    'l1:thm:main': ('l1:lem:reduce', 'l2:thm:main', 'l1:prop:corebranch',
                   'l1:lem:earlycore', 'l1:lem:noncore'),
}


def references(source):
    source = re.sub(r'(?<!\\)%[^\n]*', '', source)
    labels = Counter(re.findall(r'\\label\{([^}]+)\}', source))
    refs = re.findall(r'\\(?:ref|eqref)\{([^}]+)\}', source)
    return labels, refs, sorted(set(refs) - labels.keys())


def topological_order(graph):
    temporary, permanent, ordered = set(), set(), []
    def visit(node):
        if node in temporary:
            raise ValueError(node)
        if node in permanent:
            return
        temporary.add(node)
        for predecessor in graph.get(node, ()):
            visit(predecessor)
        temporary.remove(node)
        permanent.add(node)
        ordered.append(node)
    for node in graph:
        visit(node)
    return ordered


def run():
    path = Path(__file__).resolve().parents[2] / 'main.tex'
    data = path.read_bytes()
    source = data.decode('utf-8')
    labels, refs, undefined = references(source)
    assert not undefined and max(labels.values()) == 1
    assert references(source + r'\ref{missing:referee-control}')[2] == ['missing:referee-control']
    order = topological_order(DEPENDENCIES)
    assert set(order) <= labels.keys()
    cyclic = dict(DEPENDENCIES, **{'l2:thm:main': ('l1:thm:main',)})
    try:
        topological_order(cyclic)
    except ValueError:
        pass
    else:
        raise AssertionError('cycle positive control escaped')
    return {'source_sha256': sha256(data).hexdigest(), 'lines': len(source.splitlines()),
            'labels': len(labels), 'ref_and_eqref_occurrences': len(refs),
            'missing_references': undefined, 'proof_dependency_edges': sum(map(len, DEPENDENCIES.values())),
            'dependency_order': order, 'positive_controls': ['undefined reference', 'theorem cycle']}
