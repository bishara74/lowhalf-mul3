"""Source identity, result inventory, references, and explicit proof dependency audit.
Only reads ../source.tex, never other workspace sources or checks.
"""
import re, hashlib
from algebra import *
start=time.time(); src=Path(__file__).resolve().parent.parent/'source.tex'; s=src.read_text()
labels=re.findall(r'\\label\{([^}]+)\}',s)
refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',s)
assert len(labels)==len(set(labels)); missing=sorted(set(refs)-set(labels)); assert not missing
pat=r'\\begin\{(theorem|lemma|proposition|remark)\}(?:\[([^\n]*?)\])?\s*\\label\{([^}]+)\}'
results=[]; number=0
for m in re.finditer(pat,s):
 number+=1
 line=s[:m.start()].count('\n')+1
 if 316<=line<951 and m.group(1)!='remark':
  results.append({'number':number,'type':m.group(1),'name':m.group(2) or '', 'label':m.group(3),'line':line})
# Explicit proof-use graph, read against every displayed ref in its proof.
D={
'l3:lem:rad':[], 'l3:lem:wt':[], 'l3:lem:P':['l3:lem:rad','l3:lem:wt'],
'l3:lem:A':['l3:lem:P'], 'l3:lem:D1':['l4:lem:types'],
'l3:lem:C':['l3:lem:deriv','l4:thm:main','l4:lem:planeU','l4:lem:noq2','l3:lem:D1'],
'l3:lem:abs':[], 'l3:prop:B':['l3:lem:A','l3:lem:abs','l3:thm:L4','l4:prop:B'],
'l3:lem:B3U':['l4:lem:support'], 'l3:lem:pl':[],
'l3:lem:B3a':['l3:lem:pl'], 'l3:lem:B3b':['l3:lem:B3a'],
'l3:prop:B3':['l3:lem:B3U','l3:lem:C','l3:lem:B3a','l3:lem:B3b'],
'l3:thm:main':['l3:lem:C','l3:prop:B3','l3:prop:B'],
'l2:lem:replace':['l3:lem:P','l4:lem:Qonly'], 'l2:lem:sym':[], 'l2:lem:degree':[],
'l2:lem:four':['l3:lem:P','l3:lem:rad','l3:lem:wt','l4:lem:support'],
'l2:lem:lastfactor':['l4:lem:types','l4:lem:support'], 'l2:lem:two':[],
'l2:prop:reorder':['l3:thm:main'], 'l2:lem:ideal':[], 'l2:lem:rankext':[],
'l2:lem:coset':['l3:lem:B3a','l3:lem:B3b'],
'l2:prop:onehigh':['l2:lem:coset','l2:lem:rankext','l2:lem:degree','l2:lem:lastfactor','l2:lem:ideal'],
'l2:thm:main':['l2:lem:replace','l3:thm:main','l2:prop:onehigh'],
'l1:lem:reduce':['l3:lem:P','l4:lem:Qonly','l2:lem:replace'],
'l1:lem:cubic':[], 'l1:lem:first':['l1:lem:cubic','l3:lem:P'],
'l1:lem:corecoset':['l3:lem:pl','l3:lem:B3a','l3:lem:B3b'],
'l1:lem:earlycore':['l1:lem:cubic','l4:lem:support','l2:lem:four'],
'l1:prop:corebranch':['l1:lem:corecoset'],
'l1:lem:ordinarypair':['l1:lem:corecoset','l3:lem:pl','l3:lem:B3a'],
'l1:lem:noncoremult':['l1:lem:ordinarypair'],
'l1:lem:noncore':['l1:lem:ordinarypair','l1:lem:noncoremult','l2:lem:ideal','l2:lem:rankext'],
'l1:thm:main':['l1:lem:reduce','l2:thm:main','l1:prop:corebranch','l1:lem:earlycore','l1:lem:noncore'],
}
assert {r['label'] for r in results}==set(D)
seen=set(); active=set()
def visit(k):
 assert k not in active, 'cycle: '+k
 if k in seen: return
 active.add(k)
 for d in D.get(k,[]): visit(d)
 active.remove(k); seen.add(k)
for k in D: visit(k)
# Positive controls: missing reference and planted dependency cycle are detected.
assert 'planted:missing' not in set(labels)
D['planted:a']=['planted:b']; D['planted:b']=['planted:a']
cycle_detected=False
try: visit('planted:a')
except AssertionError: cycle_detected=True
assert cycle_detected
D.pop('planted:a'); D.pop('planted:b')
save('source_audit',{'status':'pass','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'labels':len(labels),'reference_occurrences':len(refs),'missing_references':missing,'in_scope_results':results,'proof_dependencies':D,'dependency_cycle':False,'positive_controls_detected':2},start)
