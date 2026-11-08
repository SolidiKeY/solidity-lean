#!/usr/bin/env python3
"""Monthly first-parent committed snapshots, no tree checkouts.
Run after metrics.py: python3 docs/audits/direction-tools/census/trend.py
Monthly sample is last first-parent commit in each UTC author-independent committer month.
"""
import argparse, collections, csv, datetime, json, pathlib, re
from metrics import BASE, OUT, aggregate, blobs, dump, git, module, tree

def run(rev,out):
    log=git("log","--first-parent","--reverse","--format=%H %ct",rev).decode().splitlines()
    samples={}
    for row in log:
        sha,ts=row.split(); month=datetime.datetime.fromtimestamp(int(ts),datetime.timezone.utc).strftime("%Y-%m")
        samples[month]=sha
    census=json.loads((out/"census.json").read_text()); history=[]; previous=None; prevrev=None; cache={}
    for month,sha in sorted(samples.items()):
        paths=tree(sha); selected={p:b for p,b in paths.items() if p.startswith("Solidity/") and p.endswith(".lean")}
        missing={p:b for p,b in selected.items() if (p,b) not in cache}
        for p,t in blobs(missing).items(): cache[p,missing[p]]=module(p,t)
        mods=[cache[p,b] for p,b in selected.items()]; headline=aggregate(mods)
        areas={a:aggregate([m for m in mods if m["area"]==a]) for a in sorted({m["area"] for m in mods})}
        # Goals.lean does not exist on this base. Preserve unavailability rather than
        # interpret theorem counts, merge counts, or absent counters as goals closed.
        goals=blobs({p:b for p,b in paths.items() if p=="Solidity/Goals.lean"})
        roadmap_files=[m["path"] for m in mods if m["roadmap_commands"]]
        interval=([prevrev+".."+sha] if prevrev else [sha])
        merges=git("log","--first-parent","--merges","--format=%H %s",*interval).decode().splitlines()
        plan_merges=[x for x in merges if re.search(r"\bplan[- /]",x,re.I)]
        row={"month":month,"revision":sha,**{k:v for k,v in headline.items() if k not in ("declarations","by_category")},**headline["declarations"],"axiom_pin_lines":sum(m["lines"] for m in mods if m["category"]=="axiom_pins"),"goals_closed":None,"lines_added_per_goal_closed":None,"goal_status":"unavailable: no authoritative goal-closure parser/counter; absent file is not zero goals", "goals_file_present":bool(goals),"roadmap_command_files":roadmap_files,"merged_plan_steps_visible":len(plan_merges),"merged_plan_commits":plan_merges,"lines_delta":headline["lines"]-previous["lines"] if previous else None,"areas":areas}
        history.append(row); previous=headline; prevrev=sha
        print(month,sha,headline["files"],headline["lines"],flush=True)
    dump(out/"history.json",history)
    fields=[k for k in history[-1] if k not in ("areas","roadmap_command_files","merged_plan_commits")]
    with (out/"trend.csv").open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=fields,extrasaction="ignore"); w.writeheader(); w.writerows(history)
    first,last=history[0],history[-1]; growth=[]
    for area,end in last["areas"].items():
        start=first["areas"].get(area,{}).get("lines",0)
        growth.append({"area":area,"initial_lines":start,"final_lines":end["lines"],"added_lines":end["lines"]-start,"growth_ratio":end["lines"]/start if start else None,"goals_moved":None,"what":f"Solidity/{area}: lexical source area; goal closure unavailable; growth alone gives no direction verdict."})
    mods=[m for f in census["module_chunks"] for m in json.loads((out/f).read_text())]
    largest=sorted(mods,key=lambda x:(-x["lines"],x["path"]))[:20]
    summary={"revision":rev,"totals":census["solidity_totals"],"largest_modules":[{k:m[k] for k in ("path","lines","category","area")} | {"what":f"{m['area']} module ({m['category']}); size ranks physical source, not semantic complexity."} for m in largest],"fastest_growing_areas_by_added_lines":sorted(growth,key=lambda x:(-x["added_lines"],x["area"]))[:20],"fastest_growing_areas_by_ratio":sorted([g for g in growth if g["growth_ratio"] is not None],key=lambda x:-x["growth_ratio"])[:20],"over_3x_growth_candidates":[g for g in growth if g["growth_ratio"] is not None and g["growth_ratio"]>3],"over_3x_with_unchanged_goals":None,"direction_verdict":None,"waits":["Solidity/Goals.lean absent at pinned base and no history found; goals closed and lines/goal are unavailable, not zero.","scripts/differential/ and scripts/bench/ absent at pinned base; no corresponding outputs reused."],"limitations":["No matched real-world unit calibration is claimed by this census; whole-repository ratios to CompCert would not compare like with like.","Generated classification is a marker/path-based lower bound, unmarked includes possible generated code.","Monthly history samples only first-parent reachable commits; partial current month included; merge labels are not completed goals.","Timing sample predates base; matched module paths but changed line denominators possible; no current or area-total timing asserted."],"trend_sample_policy":"Last first-parent commit per committer UTC month; all reachable history, final month partial.","inventory":census["inventory"]}
    dump(out/"summary.json",summary)

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__); ap.add_argument("--rev",default=BASE); ap.add_argument("--out",type=pathlib.Path,default=OUT); a=ap.parse_args(); run(git("rev-parse",a.rev).decode().strip(),a.out)
