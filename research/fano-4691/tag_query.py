import ctypes
from baseline import E,N,goal
from boundary import edge_rows,maximal
from z3lib import Z
from time import monotonic

def run(k,timeout_ms,fixture=None):
    n=14
    inputs=sorted(set(edge_rows+maximal+[1,128]))
    width=len(inputs)
    ix=lambda v:f'(_ bv{v} 6)'
    bits=lambda v,w:f'(_ bv{v} {w})'
    disj=lambda xs:'(or '+' '.join(xs)+')' if xs else 'false'
    conj=lambda xs:'(and '+' '.join(xs)+')' if xs else 'true'
    def sig(i):
        return sum(((r>>i)&1)<<j for j,r in enumerate(inputs))
    def bit(vec,r):
        j=inputs.index(r)
        return f'(= ((_ extract {j} {j}) {vec}) #b1)'
    def bit_anc(vec,g):
        return f'(= ((_ extract {g} {g}) {vec}) #b1)'
    def no(vec,row):
        return f'(not {bit(vec,row)})'
    target=sum(((goal>>r)&1)<<j for j,r in enumerate(inputs))
    s=[f'(set-option :timeout {timeout_ms})','(set-logic QF_BV)']
    s.extend(['(declare-const pi (_ BitVec 6))','(declare-const lj (_ BitVec 6))',
              f'(assert (and (bvult pi {ix(k)}) (bvult lj {ix(k)}) (distinct pi lj)))'])
    for g in range(k):
        for p in ('L','R','W'):s.append(f'(declare-const {p}{g} (_ BitVec {width}))')
        for p in ('al','bl','aw'):s.append(f'(declare-const {p}{g} (_ BitVec 3))')
        for p in ('a','b'):s.append(f'(declare-const {p}{g} (_ BitVec 6))')
        s.append(f'(declare-const isAnd{g} Bool)')
        s.append(f'(assert (and (bvult a{g} b{g}) (bvult b{g} {ix(n+g)})))')
        for j in range(n+g):
            w=bits(sig(j),width) if j<n else f'W{j-n}'
            a=bits(0,3) if j<n else f'aw{j-n}'
            s.append(f'(assert (=> (= a{g} {ix(j)}) (and (= L{g} {w}) (= al{g} {a}))))')
            s.append(f'(assert (=> (= b{g} {ix(j)}) (and (= R{g} {w}) (= bl{g} {a}))))')
        s.append(f'(assert (= W{g} (ite isAnd{g} (bvand L{g} R{g}) (bvor L{g} R{g}))))')
        pre=f'(bvor al{g} bl{g})'
        s.append(f'(define-fun pure{g} () Bool '+conj([f'isAnd{g}',bit(f'W{g}',129),no(f'W{g}',1),no(f'W{g}',128)])+')')
        for name,row in (('point',1),('line',128)):
            p=conj([f'pure{g}',no(f'L{g}',row),no(f'R{g}',row)])
            s.append(f'(define-fun {name}{g} () Bool {p})')
        s.append(f'(assert (=> (= pi {ix(g)}) (and point{g} {bit_anc(pre,2)} (not {bit_anc(pre,1)}))))')
        s.append(f'(assert (=> (= lj {ix(g)}) (and line{g} {bit_anc(pre,2)} (not {bit_anc(pre,0)}))))')
        s.append(f'(assert (= aw{g} (bvor {pre} (bvor (ite (= pi {ix(g)}) #b001 #b000) (bvor (ite (= lj {ix(g)}) #b010 #b000) (ite pure{g} #b100 #b000))))))')
    s.append(f'(assert (and (= W{k-1} {bits(target,width)}) {bit_anc(f"aw{k-1}",0)} {bit_anc(f"aw{k-1}",1)}))')
    if fixture is not None:
        assert len(fixture)==k
        for g,(op,a,b) in enumerate(fixture):
            a,b=sorted((a,b))
            s.append(f'(assert (= a{g} {ix(a)}))')
            s.append(f'(assert (= b{g} {ix(b)}))')
            s.append(f'(assert (= isAnd{g} {"true" if op=="and" else "false"}))')
    s.append('(check-sat)')
    cfg=Z.Z3_mk_config()
    ctx=Z.Z3_mk_context(cfg)
    Z.Z3_del_config(cfg)
    try:
        a=Z.Z3_eval_smtlib2_string(ctx,'\n'.join(s).encode()).decode().strip()
        print('gate budget',k,'truth rows',width,'status',a,flush=True)
        if a=='sat':
            queries=' '.join(f'{p}{g}' for g in range(k) for p in ('a','b','isAnd'))
            print(Z.Z3_eval_smtlib2_string(ctx,f'(get-value ({queries}))'.encode()).decode())
        return a
    finally:Z.Z3_del_context(ctx)

if __name__=='__main__':
    run(27,75000)
