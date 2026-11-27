"""Check whether a distinguished atom can occur once in every formula of <=4 gates."""
n=5
v=[sum(((x>>i)&1)<<x for x in range(1<<n)) for i in range(n)]
cap=4
general=[set(v)]+[set() for _ in range(cap)]
zero=[set(v[1:])]+[set() for _ in range(cap)]
one=[{v[0]}]+[set() for _ in range(cap)]
for k in range(1,cap+1):
    for a in range(k):
        b=k-1-a
        for xs,ys,out in [(general[a],general[b],general[k]),
                          (zero[a],zero[b],zero[k]),
                          (one[a],zero[b],one[k])]:
            for x in xs:
                for y in ys:
                    out.update((x&y,x|y))
    allowed=set().union(*zero[:k+1],*one[:k+1])
    unhandled=general[k]-allowed
    assert not unhandled
    print(k,len(general[k]),len(unhandled),[hex(x) for x in sorted(unhandled)[:10]])
