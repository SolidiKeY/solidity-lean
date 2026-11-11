"""Occurrence-based roles preserve distinct hypotheses sharing a user name."""
def annotate_occurrences(name,binders,spec):
    assert [b["name"] for b in binders]==spec["binders"],"Full ordered binder census mismatch"
    positions=set(range(len(binders)))
    logical={i for i,b in enumerate(binders) if b["is_prop"]}
    assert logical==set(spec["premises"]),"Indexed logical premise role omitted or invented"
    configuration=set(spec["configuration"])
    assert configuration<=positions and not configuration&logical,"Invalid indexed configuration roles"
    return [dict(b,index=i,binder_id=name+"#binder-"+str(i),role=spec["premises"].get(i,
        "configuration-or-intrinsic-structure-data" if i in configuration else "correlated-per-input-data"))
        for i,b in enumerate(binders)]
