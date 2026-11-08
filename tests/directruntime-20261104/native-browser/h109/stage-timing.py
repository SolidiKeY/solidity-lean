"""Guard H109 slow-library timing against hidden gaps and cached zero-exit claims.

Pure assessment of declared observations, not an authenticated measurement
receipt. Reuses bracketed MONOTONIC/BOOTTIME arithmetic. Local budget is300s;
H134 declares600s for the entire CI slow library, never600s per member. Context,
execution, resources and cleanup still require independent authentication.
The span starts at the first check, ends at the root check, and excludes earlier
preparation/dependency setup and later cleanup; controller deadlines cover them.
"""
import sys
sys.dont_write_bytecode=True
import importlib.util
from pathlib import Path


def load(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

clock=load("stage_clock","measurement-clock.py")
plan=load("stage_plan","prepare-plan.py")
TARGETS=(*plan.SLOW,"SoliditySlowExamples")
BUDGETS={"lane-end":300_000_000_000,"ci-slow-library":600_000_000_000}


def assess(record):
    if not isinstance(record,dict) or set(record)!={"context","checks"} or record["context"] not in BUDGETS:
        raise ValueError("fixed slow-library timing context required")
    checks=record["checks"]
    if not isinstance(checks,list) or len(checks)!=len(TARGETS):
        raise ValueError("complete slow-member and root denominator required")
    budget=BUDGETS[record["context"]];intervals=[];failures=[];previous=None
    for expected,check in zip(TARGETS,checks):
        if not isinstance(check,dict) or set(check)!={"target","start","end","exitCode","cachedVerdict"}:
            raise ValueError("unknown check observation schema")
        if check["target"]!=expected:raise ValueError("slow target order or identity changed")
        if type(check["exitCode"]) is not int:raise ValueError("integer observed exit required")
        if check["cachedVerdict"] is not False:raise ValueError("cached verdict is not fresh checking")
        value=clock.compare(check["start"],check["end"],budget)
        if previous is not None:
            # Validate gaps/cross-file ordering as well as individual intervals.
            gap=clock.compare(previous,check["start"],budget)
            if not gap["clockConsistent"]:failures.append(expected+": inconsistent gap clocks")
        previous=check["end"]
        if check["exitCode"]!=0:failures.append(expected+": nonzero exit")
        if value["stopRequired"]:failures.append(expected+": clock mismatch or deadline")
        intervals.append({"target":expected,"elapsedLowerNs":value["elapsedLowerNs"],
                          "elapsedUpperNs":value["elapsedUpperNs"],"clockConsistent":value["clockConsistent"]})
    # Cumulative span includes capture brackets and every gap. Sum-of-file times
    # cannot hide scheduling/setup delay or renew the library's600s deadline.
    whole=clock.compare(checks[0]["start"],checks[-1]["end"],budget)
    if whole["stopRequired"]:failures.append("whole-library clock mismatch or deadline")
    return {"status":"declared-stage-timing-only","context":record["context"],
            "declaredBudgetNs":budget,"targetCount":len(TARGETS),"intervals":intervals,
            "cumulativeElapsedLowerNs":whole["elapsedLowerNs"],
            "cumulativeElapsedUpperNs":whole["elapsedUpperNs"],
            "timingEligibleByDeclaredPolicy":not failures,"failures":failures,
            "contextAuthenticated":False,"executionAuthenticated":False,
            "resourcesAuthenticated":False,"cleanupAuthenticated":False,
            "workerExecutionAccepted":False,
            "spanBoundary":"First slow check through root check; preparation/dependency setup and cleanup are separate.",
            "boundary":"Mathematical assessment of declared clocks/exits/coverage only. Context labels and records do not authorize CI budgets or prove fresh execution, source preservation, resources, cleanup or H127 acceptance."}
