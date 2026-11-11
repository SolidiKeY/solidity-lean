#!/usr/bin/env python3
"""All41 Path/Obs roles: frozen typed inputs plus designated checked joint packets.
No new interface coverage, generated exclusion or full acceptance is inferred.
Static binder/type pins preserve the reviewed original c6 telescope exactly.
"""
import argparse,hashlib,json,subprocess
from pathlib import Path
from census import ROOT,BASE,scan
from input_roles import annotate,digest,SPECS as BRIDGE_OUTCOME
from mutability_input_roles import SPECS as CLOSER_PAYABLE
from assignable_input_roles import SPECS as ASSIGNABLE
from pure_input_roles import SPECS as PURE
import verify_census as v
FILE="Solidity/Theory/Typed/Obs/Paths.lean"
NOTES=[
    'Types and all dependent paths coexist. Intrinsic indexing is configuration data, not a feasibility law. Lookup/strip/label equations constrain these selected inputs; anonymous arrow hypotheses remain explicit. Failed strip has a concrete separated-index input and is ordinary joint satisfiability, not an H69 contradiction.',
    'All three laws quantify every applicable location for ONE fixed L and observation pair, not every pair of observations. No ObsLoc premise occurs. The designated packet also supplies actual word and array-length locations, length one, word false and both present. Abstract observations only; no storage realizability or compiler totality follows.',
    'These specialize the global location algebra to typed Path. Actual composable paths coexist; the globally selected algebra instance is not a run-success hypothesis.',
    'L and its ObsLoc instance supply global location-algebra data WITH its laws. They coexist with one actual observation, typed locations, paths and replacement values; class inhabitation alone is not the per-input packet. Optional frame hypotheses constrain these SAME locations. No storage realization, heap execution or compiler totality is asserted.',
    'L and its ObsLoc instance supply global location-algebra data WITH its laws. They coexist with one actual observation, typed locations, paths and replacement values; class inhabitation alone is not the per-input packet. Optional frame hypotheses constrain these SAME locations. No storage realization, heap execution or compiler totality is asserted. h quantifies EVERY type and continuation below the fixed read location. The packet uses separated array indices and proves the whole universal frame together with the data; checking only the empty continuation would be insufficient.',
    'C carries intrinsic contract invariants; it is global configuration data, not admission or success. Root/location/path values are correlated per-input data. The packet selects actual StandardExample roots. Root equality, inequality and strip equations apply to those selected references; inequality is satisfiable and is not an H69 impossible-input boundary.',
    'Storage values and all typed paths/replacements are correlated data. Read/save success hypotheses describe THIS operation, not a universally successful-memory structure or compiler. Packets include real primitive replacements or a live one-element array; no target memory, gas or fork execution follows.',
    'Storage values and all typed paths/replacements are correlated data. Read/save success hypotheses describe THIS operation, not a universally successful-memory structure or compiler. Packets include real primitive replacements or a live one-element array; no target memory, gas or fork execution follows. The v binder AFTER the anonymous read-success premise is part of the full telescope and remains in the packet; the frozen theorem conclusion is not truncated at that premise.',
]
# Exact frozen binder names (including anonymous/instance binders), roles and pins.
ROWS=[
    ('Solidity.Path.append_assoc', 'T U V W p q r', 'T U V W', {}, 0, '1fde39f0850f09cf5ab49711e8358a96d7b8f3f98cdcb0e69913fe5d0725f5db', 'c0a5c56e18c7f479e66ca0c0090bfa7b4b5f9db6921e764effb96635c9659e37'),
    ('Solidity.Path.append_nil_right', 'T U p', 'T U', {}, 0, 'f5e3985ca5c2c5bc774d62e14ad4ec0be6766f1e3de31d781a64fb3f8bdeba63', 'acf6ee8d24761d828e05f16a53f16119f08da9066543b637b44403cfc295e53e'),
    ('Solidity.Path.ty_eq_of_lookup', "s f T T' h h'", 'T', {'h': 'per-input-selected-field-lookup-success', "h'": 'per-input-same-field-lookup-success'}, 0, '501ebef23a7d302d0d64e6a3d4689759d085cf308239f0d3e431cf2b811fd29e', '71fceacfd3f2e02109aa203c7dd6dd4d43a70c60af39ed08105ddd4ca9bf2a30'),
    ('Solidity.Path.strip?_append', 'T U W p r', 'T U W', {}, 0, 'b54d3217d892b210e3c01e37e2136f319d829d05c4a2d4b238acdcb36fd72dea', '53e81fdb754874f95cf62bc9f6423ea64053dbd20bb1ee1c7bdc3204f7a1503f'),
    ('Solidity.Path.eq_of_strip?', 'T U W p q r a._@._internal._hyg.0', 'T U W', {'a._@._internal._hyg.0': 'per-input-selected-path-strip-success'}, 0, 'f857dff605f5bb74bbab3e1408290893c0d97bc335154fada97e391e9da3b139', '935cb6e5dfc3ef9e0d8a9d89f29881c944e42136b467927b2a85306f1450efa8'),
    ('Solidity.Path.split_of_labels', 'T U W p q s h', 'T U W', {'h': 'per-input-selected-path-label-extension'}, 0, '9d333ad6d0363fdb44ee87c8f3c27033c6e09c5a40306fe6e2b0407fa188d59d', 'b4b0bd6fca4b3fcbd45382ccbb410806c7a36d19678959a24d779c0d23170efa'),
    ('Solidity.Path.strip?_none', 'T U W p q a._@._internal._hyg.0', 'T U W', {'a._@._internal._hyg.0': 'per-input-selected-path-strip-failure'}, 0, '2168cb989169b1ec1646c8d53aa8b9e45572c58132d5979120714eaa81c9415d', '784d19fff1271b0159ed9e859b7057130867bcfd68d0f91e12b8d85f9b3bbd5a'),
    ('Solidity.Path.strip?_append_append', 'T U V W p q r', 'T U V W', {}, 0, 'c6c76181004ce5d11eaa9bf4fe3d35b97b4011c6f5cf52a42219e721481465bd', '4e2ae3a570edab5b910ca42270df3318eba70395ec698ba3dd4569b6d854b772'),
    ('Solidity.Obs.ext', "L o o' hw hl hh", 'L', {'hw': 'all-word-locations-equality-for-fixed-observation-pair', 'hl': 'all-array-locations-equality-for-fixed-observation-pair', 'hh': 'all-typed-locations-presence-equality-for-fixed-observation-pair'}, 1, '0aadbf189e318655c41b8ed6e438dd70fc080e531ec8e6ca38ccfadca052dcad', '91d2997e9fb25de2365dc7ef0dfe5ea1610ed36cdf791b7dfe5b5a50858ba19b'),
    ('Solidity.ObsLoc.app_path', 'T U W p r', 'T U W', {}, 2, 'ba56560050f9f55c85af4080e1349a23bd311bf979f5b175fee6ba7a192f1e04', '53e81fdb754874f95cf62bc9f6423ea64053dbd20bb1ee1c7bdc3204f7a1503f'),
    ('Solidity.ObsLoc.strip?_path', 'T U W p q', 'T U W', {}, 2, '0aa631fc2a092fb1500eeb16d8124f7e52bc41738290a056b8ec034e2f64f626', '8dced5120b964c4bc75ba33c34ddb5eae96d5703d9cd22dbc0a018c8807ab12a'),
    ('Solidity.Obs.find_word', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.3761074393._hygCtx._hyg.5 o U p P r', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.3761074393._hygCtx._hyg.5 U P', {}, 3, 'df40ca25a7333a6887e62563adb7f79ec715851949afbe74e7d65b5ea56e7728', 'a5ff051e92741f46637d961909088b9d34aec6f022e962d05a57fb202bda51c4'),
    ('Solidity.Obs.find_len', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.233559244._hygCtx._hyg.5 o U p E r', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.233559244._hygCtx._hyg.5 U E', {}, 3, '8c1e2ba26a6b90db8a97866f64f0e6d84a6630aed88ceba145ee950a89bc73f5', 'c474e06550628f1e99118459ddcdad3383c4b60cfee06dc5e3a8bd303004915c'),
    ('Solidity.Obs.find_save_same', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.454566769._hygCtx._hyg.5 o U p v', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.454566769._hygCtx._hyg.5 U', {}, 3, 'e228f8560375ecea3ec56992b36ee56ff8f5bb22a42606ea1465029ee58d1f8b', '2835a893713fd94e91765c668fe5af2c0684f4afa50300d2b170904897153cb4'),
    ('Solidity.Obs.find_save_frame', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.1498439371._hygCtx._hyg.5 o U W p q v h', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.1498439371._hygCtx._hyg.5 U W', {'h': 'all-continuations-frame-for-fixed-location-pair'}, 4, '152a8498d4890869cb3804abe239456c37f76d4a45b9feb3701a92182bf3af0a', '22a7007c2d4909606af142050d3fd18cbf69cc4834fcf6a5f368d7bfd00a62d2'),
    ('Solidity.Obs.find_find', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.2259117283._hygCtx._hyg.5 o U V p q', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.2259117283._hygCtx._hyg.5 U V', {}, 3, '4d4a41812f487df5b7eeb6617d4f5f15005859e8632e2eec8b61cdd910c7823d', '49229f8e0414339f0ec2f7615c9cd5fb472ca251dd1c5b3e2e619ca8262ed2a4'),
    ('Solidity.Obs.find_nil', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.2103514582._hygCtx._hyg.5 o U p', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.2103514582._hygCtx._hyg.5 U', {}, 3, '46a66751e9027cfda6ce4f1d2271c4f6c750ed1c440c74f46df596395930a829', 'ff2330639b0c2cc3e4e5ddf0fad214e1f8af48d640bca3269b0ed5333d0c0598'),
    ('Solidity.Obs.save_find', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.158166883._hygCtx._hyg.5 o U p', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.158166883._hygCtx._hyg.5 U', {}, 3, 'd4b0793cace295041aa700b15eba5bef7e45633cd5de91c96a6e4acffca73fd0', '35480c8f4188dd19c0d81d040252586bb9495826703f9c7a419f43ad200534fc'),
    ('Solidity.Obs.save_word_below', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.1578611119._hygCtx._hyg.5 o U p P r v', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.1578611119._hygCtx._hyg.5 U P', {}, 3, '6efecb5f9fabb2539eb05f9c70c52066b1cf84d40e7d0199400afdeb9e1c2a67', '33be6ae2b4fa84d338679e941abc8fd28de0f39997e3def03e937101b7ec92e4'),
    ('Solidity.Obs.save_word_same', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.277870233._hygCtx._hyg.5 o P p v', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.277870233._hygCtx._hyg.5 P', {}, 3, 'f98464c60bbce01142170bc4ca3a4004ef5971d376b8a6beedb043e9074fd516', '46c2951f7976fa31be5a46b66f75823158d370fbf632a1310abb79585c9596cc'),
    ('Solidity.Obs.save_word_frame', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.360229847._hygCtx._hyg.5 o U p P q v h', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.360229847._hygCtx._hyg.5 U P', {'h': 'per-input-selected-word-location-separation'}, 3, '8fbfbb53e4d70533ea0d662ed4bfb649a1f0657fc3804e0da3beee26dfacfe13', '6cca297070e6fd17d1197230d46a61eb3500ec0d4539a43113447b72d5fc5ca7'),
    ('Solidity.Obs.save_len_frame', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.3051724965._hygCtx._hyg.5 o U p E q v h', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.3051724965._hygCtx._hyg.5 U E', {'h': 'per-input-selected-array-location-separation'}, 3, '2d225bf67431413b2fef7a35c6ff772d26fcb0a04fcb1084645f4c7fd6aabd85', 'd2dcbe40506f54286876da2dc8e7c3ae4037510ea6a0bd7455261428fd0ff6df'),
    ('Solidity.Obs.find_save_below', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.3304526728._hygCtx._hyg.5 o U V q r v', 'L inst._@.Solidity.Theory.Typed.Obs.Paths.3304526728._hygCtx._hyg.5 U V', {}, 3, '3192808071c80595bf557bf92c7f048ced7f4b21b738687237ee2b1369cd18d5', 'd20393e8c749d33ce6aa519780c2e79acdbde4e7c60926b7ffe098d0f3c99c02'),
    ('Solidity.SRef.ty_eq', 'C U W r q h', 'C U W', {'h': 'per-input-selected-root-equality'}, 5, 'b46d6d554a6461c2af788cae78c4360f5408a6c959334925a5601f4d2d92f6f9', 'eab2440bfb000e5ebef5549d155423223d8b00931f295c0ebe1f6dcf185707e6'),
    ('Solidity.SRef.strip?_append', 'C U W r p', 'C U W', {}, 5, 'a9b069a6b61bd43de007cbf097a69d8eadd1ae64569b6f2ec05bb53a1a280cef', '71369d83275d56b61169c984b087fbd23e2ab4e54c27ff0746d5209dfe578c0f'),
    ('Solidity.SRef.eq_of_strip?', 'C U W r q p h', 'C U W', {'h': 'per-input-selected-reference-strip-success'}, 5, '6ceecf260480fd7cff7e76f1d6a8a5205cf2f88e2bd8a40acb401ba52540fd77', 'e7bfda17aa747e8949de732421eaf913b59e63b5560d8ff44b5a0538d466936d'),
    ('Solidity.SRef.append_append', 'C U V W r p q', 'C U V W', {}, 5, '18145f270120d38735be43045fe36d4b2ba5203837c89542d4abe04574ef05d6', '1898553e97d87c6aab2088b80bd0c20cd4928ca79f68d0a720c0f85454f2e4d1'),
    ('Solidity.SRef.append_nil', 'C U r', 'C U', {}, 5, '1051edf4a87c1e495aaf503cc4011c0796cb2a01fd931365509045896f9a8c2f', '25bdd33ba8eed26c7e74434f0fdec3bb311566f3fed374382ea2547dda573754'),
    ('Solidity.SRef.strip?_append_append', 'C U V W r p q', 'C U V W', {}, 5, '4ed3645d4b5bfc097f30067e7dcade8f48ad0d701235a3bdf16d7df9f9d5dadc', 'e87a89a06fabc67883b1fcc7312d21ecbb68711bf7f9ffecdce018bbbd24dadf'),
    ('Solidity.SRef.strip?_root_ne', 'C U W r q h', 'C U W', {'h': 'per-input-selected-root-inequality'}, 5, '9b31392d1982a0dd34044abb2a025868e0b7a6e29ced13bce8b8c6b6ba80fd8f', '9f1b3a925b78212a3c67c0439322f86b0149d123eb74bfd0172cafb5b3b491e2'),
    ('Solidity.SLoc.strip?_app', 'C U W p r', 'C U W', {}, 5, '7cefec6f6b6679b48421301992efa791f73c4a3260dbb4a1164b33a5d5fa0514', 'a3eaf677d707dfa87cce6ce5f31a98d27ab8b2b64b097a5404e93b747d1a09a4'),
    ('Solidity.SLoc.eq_of_strip?', 'C U W p q r h', 'C U W', {'h': 'per-input-selected-location-strip-success'}, 5, 'af77a63bdc9f2c7ffd1c77f10ef2c4b785f94dc616c78417d2fa419de08a535c', '571244591bc0e13d350da982de7b3ceaa3ffc30d30b5fe9d1fe2a413e56aa00b'),
    ('Solidity.SLoc.app_app', 'C U V W p q r', 'C U V W', {}, 5, 'baa638bd933cc2908d284b3217b57295946302d731d13c96c8cc34c049e4476c', '3288431171e52c1235571047d60fefe1457c790834cfdf1ed82424a5637624b5'),
    ('Solidity.SLoc.app_nil', 'C U p', 'C U', {}, 5, '4a0446e0d6e70a557413185fbc51bd743959011b4981dfc68582678111d00788', '97300ca3c3fafd1cf36af7c2de88ea024e76aa7741187cc471701a80e8c2a552'),
    ('Solidity.SLoc.strip?_app_app', 'C U V W p q r', 'C U V W', {}, 5, '164acfe1ce9eb29f44f32c191286892d5884dc3a5d0377fe17bf520d7b5f5617', 'e7bf654c77e3837f19f424d880774fe7d36a27d9b94f637bcc806a4ae0802edd'),
    ('Solidity.SLoc.app_ref', 'C U W r q', 'C U W', {}, 5, '7d98213967b9f0fb96c5c2d4d0ccb0f164f676e3b6e3bb1dd1d2a81a062b4851', 'd782a95b445ea46bd69b54e3194664821cf637b817025df69abae4c592c8a7bf'),
    ('Solidity.SVal.findM_append', 'T U W x p r', 'T U W', {}, 6, '78f0f4dea339ff16c01c32529358324cfdebea338f449c5dd109375ef0205581', '2c8825e200a7219a447726e5d6938eda0d1455dd93c17c735795de7aafd9026b'),
    ('Solidity.SVal.saveM_append_eq', 'T U W x p r v', 'T U W', {}, 6, '341e03bbaf8afc8f22adb41a31bc653ad4c0b0618bacec82fbbdea260d824db7', 'f593cca1af5236e276025b62ab915062899efd556204c020c761df147c34c0d6'),
    ('Solidity.SVal.saveM_of_findM', 'T U x p y a._@._internal._hyg.0 v', 'T U', {'a._@._internal._hyg.0': 'per-input-selected-read-success'}, 7, 'fdbf7c2eff1755887364f60f3881ad9865cc868dd134c187eed460da61b8e511', '6e935f29718a6082d5b2aaaf938337513ed862bae29f83abffc698a2e4122612'),
    ('Solidity.SVal.saveM_append', "T U W x p r v x' h", 'T U W', {'h': 'per-input-selected-composed-save-success'}, 6, 'b46dc6113c67a32f82f7cd36d75ffb12d6c4bea70fb8f9f866565b03c60ec037', '83d182125f0ae2cb15f9c2166ebea031eb3b6403b4e78aaba9963792d7a55639'),
    ('Solidity.SVal.saveM_at_n', "E W y y' i r v h", 'E W', {'h': 'per-input-selected-array-save-success'}, 6, 'dae2fc7226972a9262604e1383af50dc68510d59c4b0aa82df7b08f16a89ad7a', '0482117464fd6f55593b8cc51e48c8915778d26355019630ee2009f55dc1d4d3'),
]
SPECS={name:dict(binders=bs.split(),configuration=cfg.split(),premises=props,notes=NOTES[note]) for name,bs,cfg,props,note,_,_ in ROWS}
PINS={name:dict(type_expr=ty,binders=bs) for name,_,_,_,_,ty,bs in ROWS}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ("proof-evidence","historical-evidence","out"):ap.add_argument("--"+name,type=Path,required=True)
    a=ap.parse_args();proof=a.proof_evidence.resolve();old=a.historical_evidence.resolve();out=a.out.resolve()
    if any(p.is_relative_to(ROOT) for p in (proof,old,out)):raise SystemExit("Use off-Git evidence")
    source=old/"verified-census.json";manifest=dict(line.split("  ",1)[::-1] for line in (old/"SHA256SUMS").read_text().splitlines())
    assert digest(source)==manifest[source.name],"Historical snapshot hash mismatch"
    frozen=subprocess.check_output(["git","show",BASE+":"+FILE],cwd=ROOT)
    assert (ROOT/FILE).read_bytes()==frozen,"Selected frozen interface changed"
    selected={r["source_name"]:r for r in scan(frozen.decode(),FILE)}
    assert set(selected)==set(SPECS)==set(PINS) and len(SPECS)==41
    prior=set(BRIDGE_OUTCOME)|set(CLOSER_PAYABLE)|set(ASSIGNABLE)|set(PURE)
    assert len(prior)==44 and prior.isdisjoint(SPECS)
    typed=json.loads(source.read_text());assert typed["base"]==BASE
    originals={r["source_name"]:r for r in typed["declarations"]};assert len(originals)==500
    v.VERSION=json.loads((proof/"serial/baseline-results.json").read_text())["version"];v.FINGERPRINTS.clear();v.checked_module(proof/"serial",FILE)
    records=[]
    for name,spec in SPECS.items():
        row=originals[name];bs=row["elaborated"]["binders"]
        for key in ("source_name","file","line","kind","visibility","source_header","source_header_sha256","source_prefix_sha256","proving_owner","documented_producing_lane"):
            assert row[key]==selected[name][key],"Frozen source provenance changed"
        assert row["elaborated"]["name"]==name and row["elaborated"]["module"]==FILE[:-5].replace("/","."),"Frozen elaborated identity changed"
        assert hashlib.sha256(row["elaborated"]["type_expr"].encode()).hexdigest()==row["elaborated_type_sha256"]==PINS[name]["type_expr"]
        assert hashlib.sha256(json.dumps(bs,sort_keys=True,separators=(",",":")).encode()).hexdigest()==PINS[name]["binders"],"Frozen binder metadata changed"
        report=annotate(row,spec)
        for b in report["binders"]:
            if b["name"].startswith("inst."):b["role"]="global-location-algebra-instance-data-with-laws"
        assert name in v.WITNESSES and name not in v.IMPOSSIBLE
        report["designated_joint_certificate"]=v.certificate(proof/"serial",*v.WITNESSES[name]);records.append(report)
    out.mkdir(parents=True,exist_ok=True)
    payload=dict(frozen_assignment_base=BASE,current_head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),historical_typed_snapshot_sha256=digest(source),declarations=records,reviewed_path_role_records=41,previous_disjoint_role_specifications=44,combined_disjoint_role_specifications=85,remaining_role_specifications=415,new_joint_interfaces=0,generated_candidates_dispositioned=0,full_assignment_acceptance=False,boundary="41 selected-file roles and designated joint receipts checked. Prior44 specification names checked only for disjointness here; their separate acceptance snapshot remains44. Frozen original types and current proofs remain separate; no dependent-definition equivalence or physical compiler coverage.")
    (out/"path-input-roles.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("PATH_INPUT_ROLES_PASS:41checked;85disjointspecifications;415rolesremaining;0newinterfaces;full_acceptance=false")
if __name__=="__main__":main()
