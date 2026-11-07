#!/usr/bin/env python3
"""Author checked scalar ring proofs for the concrete Eisenstein identities.

The tool composes the proved integer ring and congruence laws. It supplies no
proof authority: Lim checks every auxiliary definition and final theorem.
Source modules, coefficients and output bytes have explicit bounds. Existing
kernel rules and proof/resource budgets are unchanged.
"""
import argparse
import importlib.util
import re
import sys
from dataclasses import dataclass
from pathlib import Path

_spec = importlib.util.spec_from_file_location("flt_coefficients", Path(__file__).with_name("generate-flt-cubes.py"))
_cubes = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _cubes
_spec.loader.exec_module(_cubes)
add, mul = _cubes.add, _cubes.mul
monomial = _cubes.monomial

def negative(x): return ("negative", x)
def term(item):
    variables,coefficient=item
    value=monomial(variables)
    return value if coefficient==1 else negative(value) if coefficient==-1 else mul(coefficient,value)
def polynomial(items):
    return 0 if not items else term(items[0]) if len(items)==1 else add(term(items[0]),polynomial(items[1:]))
_cubes.term=term
_cubes.polynomial=polynomial
def call(name, *args):
    return f"(#pt-app (#pt-use {name} ()) {' '.join(args)})" if args else f"(#pt-use {name} ())"
def render(x):
    if isinstance(x, str): return x
    if isinstance(x, int):
        if abs(x) > 128: raise ValueError("coefficient bound exceeded")
        value = call("integer-of-natural", f"(#pt-numeral {abs(x)})")
        return call("integer-negate",value) if x < 0 else value
    op = {"add":"integer-add", "multiply":"integer-multiply", "negative":"integer-negate"}[x[0]]
    return call(op, *(render(a) for a in x[1:]))
def equality(a,b): return call("integer-equal",render(a),render(b))
def ground(x):
    if isinstance(x,int): return max(x,0),max(-x,0)
    if isinstance(x,str): raise ValueError("not closed")
    a=ground(x[1])
    if x[0]=="negative": return a[1],a[0]
    b=ground(x[2])
    if x[0]=="add": return a[0]+b[0],a[1]+b[1]
    return a[0]*b[0]+a[1]*b[1],a[0]*b[1]+a[1]*b[0]

@dataclass(frozen=True)
class Evidence:
    left: object
    right: object
    term: str
    depth: int

class IntegerPolynomialBuilder(_cubes.CoefficientBuilder):
    HELPERS_PER_MODULE=384
    def __init__(self,stem):
        super().__init__()
        self.stem=stem; self.next_helper=0
    def emit(self,left,right,proof,depth):
        key=(left,right)
        if key in self.cache: return self.cache[key]
        if len(proof)>4096 or depth>26:
            if len(self.helpers)==self.HELPERS_PER_MODULE:
                raise ValueError("authoring helper bound exceeded")
            name=f"scalar-ring-step-{self.next_helper:04}"
            self.next_helper+=1
            bs=" ".join(f"({v} (#pt-use integer ()))" for v in self.variables)
            self.helpers.append(f"(#math-definition {name} () (#pt-pi ({bs}) {equality(left,right)}) (#pt-lambda ({bs}) {proof}))")
            proof=call(name,*self.variables); depth=3
        result=Evidence(left,right,proof,depth); self.cache[key]=result
        return result
    def reflexivity(self,x,right=None):
        right=x if right is None else right
        proof=call("integer-reflexive",render(x))
        if x!=right:
            try: a,b=ground(x),ground(right)
            except ValueError: pass
            else:
                n=a[0]+b[1]
                if n!=b[0]+a[1] or n>128: raise ValueError("invalid or oversized closed equality")
                proof=f"(#pt-refl #pt-nat (#pt-numeral {n}))"
        # Open differing endpoints occur only for definitional zero shapes;
        # their convertibility is independently checked by the kernel.
        return self.emit(x,right,proof,2)
    def transitive(self,a,b):
        if a.right!=b.left: raise ValueError("equality endpoints do not match")
        if a.left==a.right: return b
        if b.left==b.right: return a
        return self.emit(a.left,b.right,call("integer-transitive",render(a.left),render(a.right),render(b.right),a.term,b.term),1+max(a.depth,b.depth))
    def symmetric(self,p):
        return self.emit(p.right,p.left,call("integer-symmetric",render(p.left),render(p.right),p.term),1+p.depth)
    def binary(self,op,a,b):
        if a.left==a.right and b.left==b.right: return self.reflexivity(op(a.left,b.left))
        name="integer-add-congruent" if op is add else "integer-multiply-congruent"
        return self.emit(op(a.left,b.left),op(a.right,b.right),call(name,render(a.left),render(b.left),render(a.right),render(b.right),a.term,b.term),1+max(a.depth,b.depth))
    def congruent(self,context,p):
        marker="authoring-input"
        def contains(x):
            return x==marker or (isinstance(x,tuple) and any(contains(a) for a in x[1:]))
        def walk(x):
            if x==marker: return p
            if not contains(x): return self.reflexivity(x)
            if x[0]=="negative":
                q=walk(x[1])
                return self.emit(negative(q.left),negative(q.right),call("integer-negate-congruent",render(q.left),render(q.right),q.term),1+q.depth)
            return self.binary(add if x[0]=="add" else mul,walk(x[1]),walk(x[2]))
        return walk(context(marker))
    def lemma(self,name,args,left,right):
        names={"add-zero-right":"integer-add-zero","add-commutative":"integer-add-commutative","add-associative":"integer-add-associative","multiply-zero-right":"integer-multiply-zero","multiply-one-right":"integer-multiply-one","multiply-one-left":"integer-one-multiply","multiply-associative":"integer-multiply-associative","multiply-add-left":"integer-multiply-distributive","multiply-add-right":"integer-multiply-distribute-second","multiply-commutative":"integer-multiply-commutative"}
        if name in ("add-left-commutative","multiply-left-commutative"):
            a,b,c=args; op,prefix=(add,"add") if name.startswith("add") else (mul,"multiply")
            p=self.symmetric(self.lemma(prefix+"-associative",[a,b,c],op(op(a,b),c),op(a,op(b,c))))
            q=self.congruent(lambda x:op(x,c),self.lemma(prefix+"-commutative",[a,b],op(a,b),op(b,a)))
            r=self.lemma(prefix+"-associative",[b,a,c],op(op(b,a),c),op(b,op(a,c)))
            return self.transitive(self.transitive(p,q),r)
        return self.emit(left,right,call(names[name],*(render(x) for x in args)),3)
    def combine_equal(self,first,second):
        variables,a=first; other,b=second
        assert variables==other
        if abs(a+b)>128: raise ValueError("coefficient bound exceeded")
        value=monomial(variables)
        expanded=self.binary(add,self.expand_coefficient(first),self.expand_coefficient(second))
        p=self.symmetric(self.lemma("multiply-add-left",[a,b,value],mul(add(a,b),value),add(mul(a,value),mul(b,value))))
        q=self.congruent(lambda x:mul(x,value),self.reflexivity(add(a,b),a+b))
        proof=self.transitive(self.transitive(expanded,p),q)
        if a+b==0:
            return None,self.transitive(proof,self.emit(mul(0,value),0,call("integer-zero-multiply",render(value)),3))
        return (variables,a+b),self.transitive(proof,self.contract_coefficient(variables,a+b))
    def expand_coefficient(self,item):
        variables,a=item; x=monomial(variables)
        return self.symmetric(self.contract_coefficient(variables,a))
    def contract_coefficient(self,variables,a):
        x=monomial(variables)
        if a==1: return self.lemma("multiply-one-left",[x],mul(1,x),x)
        if a==-1: return self.emit(mul(-1,x),negative(x),call("integer-minus-one-multiply",render(x)),3)
        return self.reflexivity(mul(a,x))
    def insert_term(self,first,ordered):
        source=(first,)+ordered
        if not ordered or first[0]<ordered[0][0]: return source,self.reflexivity(polynomial(source))
        if first[0]>ordered[0][0]:
            a,b=term(first),term(ordered[0])
            if len(ordered)==1: return (ordered[0],first),self.lemma("add-commutative",[a,b],add(a,b),add(b,a))
            rest=polynomial(ordered[1:])
            p=self.lemma("add-left-commutative",[a,b,rest],polynomial(source),add(b,add(a,rest)))
            tail,q=self.insert_term(first,ordered[1:])
            proof=self.transitive(p,self.congruent(lambda x:add(b,x),q))
            if not tail: proof=self.transitive(proof,self.lemma("add-zero-right",[b],add(b,0),b))
            return (ordered[0],)+tail,proof
        combined,p=self.combine_equal(first,ordered[0])
        if len(ordered)==1: return (() if combined is None else (combined,)),p
        a,b,tail=term(first),term(ordered[0]),polynomial(ordered[1:])
        q=self.symmetric(self.lemma("add-associative",[a,b,tail],add(add(a,b),tail),add(a,add(b,tail))))
        proof=self.transitive(q,self.congruent(lambda x:add(x,tail),p))
        if combined is None: return ordered[1:],self.transitive(proof,self.reflexivity(add(0,tail),tail))
        return (combined,)+ordered[1:],proof
    def order_terms(self,items):
        if len(items)<=1: return items,self.reflexivity(polynomial(items))
        tail,p=self.order_terms(items[1:])
        head=term(items[0])
        lifted=self.congruent(lambda x:add(head,x),p)
        if not tail:
            return (items[0],),self.transitive(lifted,self.lemma("add-zero-right",[head],add(head,0),head))
        result,q=self.insert_term(items[0],tail)
        return result,self.transitive(lifted,q)
    def multiply_terms(self,first,second):
        m,a=first; n,b=second
        if not 0<abs(a*b)<=128: raise ValueError("coefficient bound exceeded")
        x,y=monomial(m),monomial(n)
        variables,ordered=self.ordered(m+n,True)
        combined=self.transitive(self.append(m,n,True),ordered)
        if abs(a)==abs(b)==1:
            left=mul(term(first),term(second))
            if a==b==1: return ((variables,1),),combined
            law="integer-multiply-two-negatives" if a==b==-1 else "integer-multiply-negative" if a==-1 else "integer-multiply-negative-second"
            middle=mul(x,y) if a==b else negative(mul(x,y))
            p=self.emit(left,middle,call(law,render(x),render(y)),3)
            q=combined if a==b else self.congruent(negative,combined)
            return ((variables,a*b),),self.transitive(p,q)
        expanded=self.binary(mul,self.expand_coefficient(first),self.expand_coefficient(second))
        p=self.lemma("multiply-associative",[a,x,mul(b,y)],mul(mul(a,x),mul(b,y)),mul(a,mul(x,mul(b,y))))
        q=self.congruent(lambda z:mul(a,z),self.lemma("multiply-left-commutative",[x,b,y],mul(x,mul(b,y)),mul(b,mul(x,y))))
        r=self.symmetric(self.lemma("multiply-associative",[a,b,mul(x,y)],mul(mul(a,b),mul(x,y)),mul(a,mul(b,mul(x,y)))))
        s=self.congruent(lambda z:mul(z,mul(x,y)),self.reflexivity(mul(a,b),a*b))
        t=self.congruent(lambda z:mul(a*b,z),combined)
        p=self.transitive(expanded,p)
        for proof in (q,r,s,t): p=self.transitive(p,proof)
        return ((variables,a*b),),self.transitive(p,self.contract_coefficient(variables,a*b))
    def normalize(self,x):
        if isinstance(x,str): return (((x,),1),),self.reflexivity(x)
        if isinstance(x,int) and abs(x)==1: return (((),x),),self.reflexivity(x,term(((),x)))
        if isinstance(x,tuple) and x[0]=="negative":
            value=x[1]
            p=self.symmetric(self.emit(mul(-1,value),negative(value),call("integer-minus-one-multiply",render(value)),3))
            terms,q=self.normalize(mul(-1,value))
            return terms,self.transitive(p,q)
        return super().normalize(x)
    def theorem(self,name,variables,left,right):
        self.variables=variables
        self.origins=[f"scripts/generate-flt-eisenstein-algebra.py:{sys._getframe(1).f_lineno}"]
        l,p=self.normalize(left); r,q=self.normalize(right)
        if l!=r: raise ValueError(f"{name}: candidate identity is false")
        proof=self.transitive(p,self.symmetric(q))
        bs=" ".join(f"(#parameter {x} (#pt-use integer ()))" for x in variables)
        self.theorems.append(f"(#theorem {name} (#universes) (#parameters {bs}) (#statement {equality(left,right)}) (#proof {proof.term}))")
    def source(self):
        aliases={n:"integer-defs" for n in ("integer","integer-of-natural","integer-equal","integer-add","integer-multiply","integer-negate")}
        aliases.update({n:"integer-equality" for n in ("integer-reflexive","integer-symmetric","integer-transitive","integer-add-congruent","integer-negate-congruent")})
        aliases.update({n:"integer-addition" for n in ("integer-add-zero","integer-add-associative","integer-add-commutative")})
        aliases.update({n:"integer-multiplication" for n in ("integer-multiply-zero","integer-multiply-one","integer-multiply-associative","integer-multiply-commutative","integer-multiply-distributive","integer-multiply-congruent")})
        aliases.update({"integer-multiply-distribute-second":"integer-divisibility-addition","integer-one-multiply":"integer-bezout-algebra","integer-zero-multiply":"integer-bezout-algebra","integer-minus-one-multiply":"integer-linear-identities"})
        aliases.update({"integer-multiply-negative":"integer-multiplication","integer-multiply-negative-second":"integer-divisibility","integer-multiply-two-negatives":"integer-divisibility"})
        body="\n\n".join(self.helpers+self.theorems)
        source="; Generated by scripts/generate-flt-eisenstein-algebra.py; native checked proof terms.\n; Generated from:\n"+"".join(f"; {o}\n" for o in self.origins)
        source+="".join(f"(#alias {n} = ./{m}.lim::{n})\n" for n,m in aliases.items())+"\n"+body+"\n"
        if len(source.encode())>8*1024*1024: raise ValueError("source-size bound exceeded")
        return source

@dataclass(frozen=True)
class Eisenstein:
    real: object
    omega: object
    def __add__(self,other): return Eisenstein(add(self.real,other.real),add(self.omega,other.omega))
    def __neg__(self): return Eisenstein(negative(self.real),negative(self.omega))
    def __mul__(self,other):
        bd=negative(mul(self.omega,other.omega))
        return Eisenstein(add(mul(self.real,other.real),bd),add(add(mul(self.real,other.omega),mul(self.omega,other.real)),bd))

def ring_laws():
    a,b,c=[Eisenstein(n+"-real",n+"-omega") for n in ("first","second","third")]
    return [("commutative",(a,b),a*b,b*a),("associative",(a,b,c),(a*b)*c,a*(b*c)),("distributive",(a,b,c),(a+b)*c,a*c+b*c),("negative",(a,b),(-a)*b,-(a*b))]

def generate_sources():
    result={}
    for law,operands,left,right in ring_laws():
        variables=tuple(v for operand in operands for v in (operand.real,operand.omega))
        for coordinate in ("real","omega"):
            stem=f"eisenstein-product-{law}-{coordinate}"
            builder=IntegerPolynomialBuilder(stem)
            builder.theorem(stem,variables,getattr(left,coordinate),getattr(right,coordinate))
            result[stem+".lim"]=builder.source()
    a,b,k="real-coordinate","omega-coordinate","factor"
    u,v=add(b,negative(add(k,k))),negative(k)
    def lambda_real(u,v): return add(mul(-1,u),negative(mul(1,v)))
    def lambda_omega(u,v): return add(add(mul(-1,v),mul(1,u)),negative(mul(1,v)))
    scalar_identities=[
        ("lambda-product-coordinate-sum",(a,b),add(lambda_real(a,b),lambda_omega(a,b)),mul(3,negative(b))),
        ("lambda-factor-real",(b,k),lambda_real(u,v),add(mul(3,k),negative(b))),
        ("lambda-factor-omega",(b,k),lambda_omega(u,v),b),
        ("coordinate-sum-product",("first-real","first-omega","second-real","second-omega"),
         add((Eisenstein("first-real","first-omega")*Eisenstein("second-real","second-omega")).real,(Eisenstein("first-real","first-omega")*Eisenstein("second-real","second-omega")).omega),
         add(mul(add("first-real","first-omega"),add("second-real","second-omega")),negative(mul(3,mul("first-omega","second-omega"))))),
        ("right-difference-cancel",(a,b),add(add(a,b),negative(b)),a),
    ]
    for label,variables,left,right in scalar_identities:
        stem="eisenstein-scalar-"+label
        builder=IntegerPolynomialBuilder(stem)
        builder.theorem(stem,variables,left,right)
        result[stem+".lim"]=builder.source()
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--check",action="store_true"); args=parser.parse_args()
    root=Path(__file__).resolve().parent.parent/"theorems/flt"
    def tokens(text): return re.findall(r"[()]|[^()\s]+",re.sub(r";[^\n]*","",text))
    def origins(text): return [line.strip() for line in text.splitlines() if line.strip().startswith("; scripts/generate-flt-eisenstein-algebra.py:")]
    generated=generate_sources()
    for path in [*root.glob("eisenstein-product-*.lim"),*root.glob("eisenstein-scalar-*.lim")]:
        if path.name not in generated:
            if not path.read_text().startswith("; Generated by scripts/generate-flt-eisenstein-algebra.py;"):
                raise SystemExit(f"{path.name}: unexpected non-generated source")
            if args.check: raise SystemExit(f"{path.name}: stale generated source")
            path.unlink()
    for name,source in generated.items():
        path=root/name; current=path.read_text() if path.is_file() else None
        matches=current is not None and tokens(current)==tokens(source) and origins(current)==origins(source)
        if args.check:
            if not matches: raise SystemExit(f"{name}: source differs; regenerate with this script")
        elif not matches: path.write_text(source)

if __name__=="__main__": main()
