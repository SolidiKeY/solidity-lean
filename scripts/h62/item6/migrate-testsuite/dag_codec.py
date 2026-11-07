"""Validate structural Expr DAGs and hash their content, independent of node IDs."""
import hashlib,json,re

def nat_text(x): return isinstance(x,str) and re.fullmatch(r'0|[1-9][0-9]*',x) is not None

def name_ok(x):
    if not isinstance(x,list): return False
    if x==['anonymous']: return True
    return len(x)==3 and name_ok(x[1]) and ((x[0]=='str' and isinstance(x[2],str)) or (x[0]=='num' and nat_text(x[2])))

def level_ok(x):
    if not isinstance(x,list) or not x: return False
    if x==['zero']: return True
    if x[0]=='succ': return len(x)==2 and level_ok(x[1])
    if x[0] in ('max','imax'): return len(x)==3 and level_ok(x[1]) and level_ok(x[2])
    return len(x)==2 and x[0] in ('param','mvar') and name_ok(x[1])

def prere_ok(x):
    return isinstance(x,list) and ((len(x)==2 and x[0]=='namespace' and name_ok(x[1])) or (len(x)==3 and x[0]=='decl' and name_ok(x[1]) and isinstance(x[2],list) and all(isinstance(v,str) for v in x[2])))

def syntax_ok(x):
    if not isinstance(x,list) or not x: return False
    if x==['missing']: return True
    if x[0]=='node': return len(x)==3 and name_ok(x[1]) and isinstance(x[2],list) and all(syntax_ok(v) for v in x[2])
    if x[0]=='atom': return len(x)==2 and isinstance(x[1],str)
    return len(x)==4 and x[0]=='ident' and isinstance(x[1],str) and name_ok(x[2]) and isinstance(x[3],list) and all(prere_ok(v) for v in x[3])

def value_ok(x):
    if not isinstance(x,list) or len(x)!=2: return False
    tag,value=x
    if tag=='string': return isinstance(value,str)
    if tag=='bool': return type(value) is bool
    if tag=='name': return name_ok(value)
    if tag=='nat': return nat_text(value)
    if tag=='int': return isinstance(value,str) and re.fullmatch(r'0|-?[1-9][0-9]*',value) is not None
    return tag=='syntax' and syntax_ok(value)

def metadata_ok(x):
    if not isinstance(x,list): return False
    if not all(isinstance(pair,list) and len(pair)==2 and name_ok(pair[0]) and value_ok(pair[1]) for pair in x): return False
    keys=[json.dumps(pair[0],sort_keys=True,separators=(',',':')) for pair in x]
    return len(set(keys))==len(keys)

def payload_ok(tag,data):
    if tag in ('bvar','nat'): return nat_text(data)
    if tag in ('fvar','mvar'): return name_ok(data)
    if tag=='sort': return level_ok(data)
    if tag=='const': return isinstance(data,list) and len(data)==2 and name_ok(data[0]) and isinstance(data[1],list) and all(level_ok(u) for u in data[1])
    if tag=='app': return data is None
    if tag in ('lam','forallE'): return isinstance(data,list) and len(data)==2 and name_ok(data[0]) and data[1] in ('default','implicit','strictImplicit','instImplicit')
    if tag=='letE': return isinstance(data,list) and len(data)==2 and name_ok(data[0]) and type(data[1]) is bool
    if tag=='str': return isinstance(data,str)
    if tag=='mdata': return metadata_ok(data)
    if tag=='proj': return isinstance(data,list) and len(data)==2 and name_ok(data[0]) and nat_text(data[1])
    return False

class DagStore:
    def __init__(self,allowed): self.allowed=set(allowed);self.hashes={};self.closed={}
    def add(self,row):
        if not isinstance(row,dict) or set(row)!={'module','id','tag','data','children'}: raise ValueError('INVALID_NODE_SCHEMA')
        module=row['module'];index=row['id'];tag=row['tag'];children=row['children']
        if not isinstance(module,str) or module not in self.allowed or module in self.closed: raise ValueError('INVALID_NODE_MODULE')
        hashes=self.hashes.setdefault(module,[])
        arities={'bvar':0,'fvar':0,'mvar':0,'sort':0,'const':0,'app':2,'lam':2,'forallE':2,'letE':3,'nat':0,'str':0,'mdata':1,'proj':1}
        if type(index) is not int or index!=len(hashes) or not isinstance(tag,str) or tag not in arities: raise ValueError('INVALID_NODE_ID_OR_TAG')
        if not isinstance(children,list) or len(children)!=arities[tag] or any(type(c) is not int or c<0 or c>=index for c in children): raise ValueError('INVALID_NODE_EDGES')
        if not payload_ok(tag,row['data']): raise ValueError('INVALID_NODE_PAYLOAD')
        data=row['data']
        if tag=='mdata': data=sorted(data,key=lambda pair:json.dumps(pair[0],sort_keys=True,separators=(',',':')))
        content={'tag':tag,'data':data,'children':[hashes[c] for c in children]}
        encoded=json.dumps(content,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode()
        hashes.append(hashlib.sha256(encoded).hexdigest())
    def root(self,module,index):
        if module in self.closed or module not in self.hashes or type(index) is not int or not 0<=index<len(self.hashes[module]): raise ValueError('INVALID_EXPRESSION_ROOT')
        return self.hashes[module][index]
    def finish(self,module):
        if module in self.closed: raise ValueError('DUPLICATE_MODULE_REPORT')
        self.closed[module]=len(self.hashes.pop(module,[]))
