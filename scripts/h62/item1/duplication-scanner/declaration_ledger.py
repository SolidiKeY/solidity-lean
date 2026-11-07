#!/usr/bin/env python3
"""Guard omitted constants, dropped lexical rows and guessed generated identities.

Structural accounting of a completed source/range/type observation only. Callers
must authenticate fresh producer execution separately; matching range fragments
never promote unlinked, private, metadata-refused or ownership-unverified rows.
"""
from collections import Counter
import bind_project_closure as closure


def keyed(rows):
    result={}
    for row in rows:
        key=closure.leaf.kernel.name_key(row["declaration"])
        if key in result:raise ValueError("duplicate declaration identity")
        result[key]=row
    return result


def account(source,lexical,legacy,bindings,source_path,module):
    """Structural accounting only; saved packets do not authenticate execution."""
    expected=closure.leaf.source_binding.join_locations(source,lexical,legacy["census"],legacy["locations"],module)
    if expected!=bindings:raise ValueError("source binding correspondence drift")
    known=keyed(legacy["census"]["rows"]);locations=keyed(legacy["locations"]["rows"])
    linked={};sources=[]
    for index,(row,bound) in enumerate(zip(lexical,bindings["rows"])):
        if row["path"]!=source_path:raise ValueError("foreign lexical source")
        sources.append({"index":index,"lexical":row,"legacy_binding":bound,"ownership":"unverified","body_equivalence":"unproved"})
        if bound["status"]=="direct-source-signature-link":
            key=closure.leaf.kernel.name_key(bound["declaration"])
            if key in linked:raise ValueError("multiple source rows claim one declaration")
            linked[key]=index
    constants=[]
    for key,row in known.items():
        selection=locations[key]["selection"];fragment=None
        if key in linked:
            state="existing-direct-source-link"
        elif selection is None:
            state="no-compiler-range"
        else:
            fragment=closure.leaf.source_binding.source_slice(source,selection)
            if key[-1]!=("str",fragment):state="range-name-differs"
            else:state="direct-range-without-legacy-link"
        constants.append({"legacy":row,"selection":selection,
                          "source_evidence":{"status":state,"lexical_index":linked.get(key),"selected_fragment":fragment},
                          "ownership":"unverified","unloaded_private_coverage":"unproved"})
    if len(constants)!=bindings["visible_kernel_total"] or len(sources)!=bindings["lexical_total"]:raise ValueError("accounting cardinality drift")
    return {"schema":1,"kind":"lossless-project-declaration-ledger","source_path":source_path,"source_sha256":bindings["source_sha256"],
            "lexical_total":len(sources),"kernel_total":len(constants),"legacy_links":len(linked),"sources":sources,"constants":constants,
            "source_evidence_counts":dict(Counter(r["source_evidence"]["status"] for r in constants)),
            "lexical_binding_statuses":dict(Counter(r["legacy_binding"]["status"] for r in sources)),
            "legacy_type_statuses":dict(Counter(r["legacy"]["status"] for r in constants)),
            "boundary":"Every observed imported constant and selected lexical row counted once. Range categories are observations, not generated-identity inference, global/private completeness, signature promotion, ownership, feasibility or body equivalence. Original792 obligations and Lean timing STOP unchanged."}

