"""A genuine circuit disproving 'every two-window charge is a whole-set refund'."""
from itertools import combinations

n = 8
a,b,c,p,q,u,v,w = range(n)
Y = {a,b,c}
S = [{a,p,q},{u,v,w}]
gates = []

def gate(op, *inputs):
    gates.append((op,inputs))
    return n+len(gates)-1

h = gate('and', gate('and',a,b),c)
nt = gate('not',h)
ap = gate('or',a,p)
left = gate('and',nt,ap)
uv = gate('or',u,v)
right = gate('and',h,uv)
mixed = gate('or',left,right)
out_l = gate('or',gate('or',mixed,h),q)
out_h = gate('or',gate('or',gate('and',mixed,h),gate('and',nt,uv)),w)

def run(xs):
    wires = [i in xs for i in range(n)]
    for op,args in gates:
        signals = [wires[j] for j in args]
        value = (all(signals) if op=='and' else any(signals) if op=='or' else not signals[0])
        wires.append(value)
    return wires

for k in range(n+1):
    for xs in combinations(range(n),k):
        val=run(xs)
        assert [val[j] for j in [out_l,out_h]]==[bool(set(xs)&s) for s in S]
        if k < len(Y): assert val[nt]
assert not run(Y)[nt]
outside=set(range(n))-Y
light={g:{i for i in range(n) if run({i})[g]} for g in range(n,n+len(gates))}
heavy={g:{i for i in outside if run(Y|{i})[g]} for g in light}
A={g for g in light if light[g]<=S[0] and len(light[g])>=2}
B={g for g in heavy if heavy[g]<=S[1] and len(heavy[g])>=2}
R={g for g in light if light[g] in S and heavy[g]==S[1]}
assert min(len(Y),len(S[0]))<=len(A)+1 and len(S[1])<=len(B)+1
assert mixed in A&B and mixed not in R
assert light[mixed]=={a,p} and heavy[mixed]=={u,v}
lhs=min(len(Y),len(S[0]))+len(S[1])
assert lhs<=len(gates)+len(R)+len(S)
used={out_l,out_h}
for g in range(n+len(gates)-1,n-1,-1):
    if g in used: used.update(gates[g-n][1])
assert set(range(n,n+len(gates)))<=used
print('inputs',n,'gates',len(gates),'mixed gate',mixed-n,'A',len(A),'B',len(B),'refunds',len(R))
print('all 256 inputs pass, all gates reach outputs; target inequality',lhs,'<=',len(gates)+len(R)+len(S))
