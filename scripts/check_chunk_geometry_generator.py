#!/usr/bin/env python3
"""Python-only generator controls; all repository writes are intercepted."""
from pathlib import Path
from unittest.mock import patch
from contextlib import redirect_stdout
from io import StringIO
import hashlib, importlib, json, re, sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
gen=importlib.import_module('generate_chunked_odd_geometry')
base=importlib.import_module('generate_odd_geometry')
def require(ok,message):
    if not ok:raise RuntimeError(message)
def without_async(s):return s.replace('set_option Elab.async false\n','')
original_read=Path.read_text
results=[]
for q in [215,437]:
    data_path=ROOT/f'NK/Certificates/Odd{q}Data.lean'
    flat_path=ROOT/f'certificates/square/data/odd{q}.txt'
    output_path=ROOT/f'NK/Certificates/Odd{q}Geometry.lean'
    data=data_path.read_text();flat=flat_path.read_text();actual=output_path.read_text()
    writes=[]
    def capture(path,text,*args,**kwargs):writes.append((Path(path),text));return len(text)
    with patch.object(Path,'write_text',capture):
        generated=gen.generate(q)
    require(writes==[(output_path,generated)],'Standalone must write exactly geometry')
    require(without_async(generated)==without_async(actual),'Generated mathematical output changed')
    require('set_option Elab.async false\n' in generated,'Asynchronous elaboration was not disabled')
    writes=[]
    with patch.object(Path,'write_text',capture),patch.object(base,'measure',lambda *a,**kw:0),redirect_stdout(StringIO()):
        base.emit(q)
    geometry_writes=[text for path,text in writes if path==output_path]
    require(geometry_writes==[generated],'Main must write exactly one chunked geometry file')
    require(writes[-1][0]==output_path,'Main final write must be chunked geometry')
    require(next(text for path,text in writes if path==data_path)==data,'Main changed data')
    leaf=re.search(r'(\.leaf ⟨\(\[[^\]]*\], \[[^\]]*\]\), \d+, )(\d+)(⟩)',data)
    require(leaf is not None,'No literal leaf')
    changed_body=data[:leaf.start(2)]+str(int(leaf.group(2))+1)+data[leaf.end(2):]
    declaration=re.search(rf'^def odd{q}Tree_\d+ : PairCertificateTree :=\n  [^\n]+\n',data,re.M)
    require(declaration is not None,'No named data declaration')
    alias=re.search(rf'^def odd{q}Tree : PairCertificateTree := (\w+)$',data,re.M)
    require(alias is not None,'No root alias')
    first_name=re.search(r'def (\w+) ',declaration.group()).group(1)
    require(first_name!=alias.group(1),'Mutation needs a proper subtree')
    wrong_alias=data[:alias.start(1)]+first_name+data[alias.end(1):]
    lines=flat.splitlines();first=lines[1].split();first[7]=str(int(first[7])+1);lines[1]=' '.join(first)
    changed_flat='\n'.join(lines)+'\n'
    mutations={
      'changed_literal_width':(data_path,changed_body,'literal bodies differ'),
      'missing_node':(data_path,data[:declaration.start()]+data[declaration.end():],'literal bodies differ'),
      'duplicate_node':(data_path,data+declaration.group(),'literal bodies differ'),
      'extra_node':(data_path,data+declaration.group().replace(first_name,f'odd{q}Tree_999999'),'literal bodies differ'),
      'wrong_root_alias':(data_path,wrong_alias,'root alias differs'),
      'duplicate_root_alias':(data_path,data+alias.group()+'\n','root alias differs'),
      'changed_flat_width':(flat_path,changed_flat,'literal bodies differ')}
    for label,(mutated_path,mutated,expected) in mutations.items():
        writes=[]
        def altered_read(path,*args,**kwargs):
            return mutated if Path(path)==mutated_path else original_read(path,*args,**kwargs)
        with patch.object(Path,'read_text',altered_read),patch.object(Path,'write_text',capture):
            try:gen.generate(q)
            except ValueError as error:require(expected in str(error),'Wrong mutation error '+label+': '+str(error))
            else:raise RuntimeError('Mutation accepted: '+label)
        require(not writes,'Rejected mutation wrote output: '+label)
    results.append({'q':q,'mathematical_output_unchanged':True,'main_geometry_writes':1,
                    'mutation_rejections':list(mutations),'output_sha256':hashlib.sha256(generated.encode()).hexdigest()})
print(json.dumps({'status':'PASS','python_optimized':not __debug__,'lean_builds_run':0,
                  'repository_writes':0,'results':results},indent=2))
