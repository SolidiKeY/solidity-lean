"""Conservative source-only constraint search; no Lean name resolution or elaboration."""
import hashlib,re

def code_only(text):
    # Preserve offsets and lines while blanking nested comments and quoted strings.
    out=list(text);i=0;depth=0;quoted=False
    while i<len(text):
        if depth:
            if text.startswith("/-",i):out[i:i+2]="  ";depth+=1;i+=2;continue
            if text.startswith("-/",i):out[i:i+2]="  ";depth-=1;i+=2;continue
            if text[i]!="\n":out[i]=" "
            i+=1;continue
        if quoted:
            if text[i]=="\\":
                out[i]=" ";i+=1
                if i<len(text) and text[i]!="\n":out[i]=" "
            elif text[i]=='"':out[i]=" ";quoted=False
            elif text[i]!="\n":out[i]=" "
            i+=1;continue
        char=re.match(r"'(?:\\.|[^\\'\n])'",text[i:]) if text[i]=="'" else None
        if char:
            n=len(char[0]);out[i:i+n]=" "*n;i+=n;continue
        raw=re.match(r'r(#+)"',text[i:]) if text[i]=="r" else None
        if raw:
            close='"'+raw[1];end=text.find(close,i+len(raw[0]));assert end>=0,"unterminated raw string"
            end+=len(close)
            for j in range(i,end):
                if text[j]!="\n":out[j]=" "
            i=end;continue
        if text.startswith("/-",i):out[i:i+2]="  ";depth=1;i+=2;continue
        if text.startswith("--",i):
            while i<len(text) and text[i]!="\n":out[i]=" ";i+=1
            continue
        if text[i]=='"':out[i]=" ";quoted=True
        i+=1
    assert depth==0 and not quoted,"unterminated comment/string in source scan"
    return "".join(out)

def augment(lean,specs):
    # Regression controls ensure comments, nested comments and string payloads
    # cannot be mistaken for explicit source-code references.
    sample='x /- outer /- BinOp.evalT -/ -/ "UnOp.evalT" -- ModOp.evalT\nBinOp.evalT'
    clean=code_only(sample)
    assert len(clean)==len(sample) and clean.count("\n")==sample.count("\n")
    assert clean.count("BinOp.evalT")==1 and "UnOp.evalT" not in clean and "ModOp.evalT" not in clean
    char_sample="'\"' BinOp.evalT '\\n' UnOp.evalT"
    char_clean=code_only(char_sample)
    assert len(char_clean)==len(char_sample) and "BinOp.evalT" in char_clean and "UnOp.evalT" in char_clean
    raw_sample='r#"raw " BinOp.evalT /- not comment"# UnOp.evalT'
    raw_clean=code_only(raw_sample)
    assert len(raw_clean)==len(raw_sample) and "BinOp.evalT" not in raw_clean and "UnOp.evalT" in raw_clean
    cleaned={p:code_only(s) for p,s in lean.items()}
    for m in specs:
        prefix=cleaned[m["path"]].splitlines()[:m["line"]-1];stack=[]
        for line in prefix:
            n=re.match(r"^namespace ([\w.]+)\s*$",line)
            if n:stack.append(n[1])
            elif re.match(r"^end(?: [\w.]+)?\s*$",line) and stack:stack.pop()
        qualified=".".join(stack+[m["definition"]])
        m["qualified_definition"]=qualified
    refs={}
    for symbol in sorted({m["qualified_definition"] for m in specs}):
        alias=symbol.removeprefix("Solidity.")
        pat=re.compile(r"(?<![\w.])(?:Solidity\.)?"+re.escape(alias)+r"(?![\w.])")
        found=[]
        for path,code in cleaned.items():
            for i,line in enumerate(code.splitlines(),1):
                if pat.search(line):found.append({"path":path,"line":i})
        refs[symbol]=found
    # Stronger candidates found outside the initially searched example directory.
    overrides={
      "M06":("Solidity/Calculus/QuotientCut.lean","theorem mod_zero","mod_zero: every admitted numeric zero divisor must fail"),
      "M26":("Solidity/Calculus/QuotientCut.lean","theorem int_div_neg_one","int_div_neg_one: unchanged division by -1 must equal unary negation"),
      "M31":("Solidity/Examples/Tactics/CheckedBlock.lean","theorem underflowChecked","underflowChecked: positive panic-recognition premise in existing consumer proof"),
      "M17":("Solidity/Optimizer/Simplify.lean","theorem lt_self","lt_self: equal operands must produce false"),
      "M18":("Solidity/Optimizer/Simplify.lean","theorem gt_self","gt_self: equal operands must produce false"),
      "M19":("Solidity/Optimizer/Simplify.lean","theorem le_self","le_self: equal operands must produce true"),
      "M20":("Solidity/Optimizer/Simplify.lean","theorem ge_self","ge_self: equal operands must produce true"),
      "M21":("Solidity/Optimizer/Simplify.lean","theorem and_true_l","and_true_l: choose a false right operand"),
      "M22":("Solidity/Optimizer/Simplify.lean","theorem or_false_l","or_false_l: choose a true right operand"),
      "M27":("Solidity/Source/Agreement/BoolSlotNot.lean","theorem bool_not_init_model","bool_not_init_model: pushed value is explicitly inverse of old operand"),
      "M29":("Solidity/Lowering/V07/WordCasts.lean","theorem to_int_eval","to_int_eval: all admitted uint256 values, including 2^255"),
      "M30":("Solidity/Lowering/V07/WordCasts.lean","theorem to_uint_eval","to_uint_eval: source wrapping cast fixes the returned word")}
    for m in specs:
        if m["id"] in overrides:
            path,anchor,name=overrides[m["id"]];source=lean[path]
            assert source.count(anchor)==1
            m["expected_failing_candidate"]={"path":path,"line":source[:source.index(anchor)].count("\n")+1,"name":name,"status":"source-level candidate; consult bounded results for execution scope and status","source_sha256":hashlib.sha256(source.encode()).hexdigest()}
        if m["id"]=="M29":
            path="Solidity/Lowering/V07/WordCastControls.lean";anchor="checkU p Semantics.intBound (-Semantics.intBound)"
            assert lean[path].count(anchor)==1
            m["boundary_control"]={"path":path,"line":lean[path][:lean[path].index(anchor)].count("\n")+1,"expression":anchor,"status":"exact threshold guard exists in pinned base; not executed"}
            m["constraint_search_result"]="Exact threshold control and all-input cast theorem found outside the initial example-only search; missing-constraint claim withdrawn"
        found=[r for r in refs[m["qualified_definition"]] if r["path"]!=m["path"]]
        m["explicit_code_mentions_first_30"]=found[:30]
        m["explicit_code_mention_count"]=len(found)
        m["explicit_code_boundary"]="Comments, ordinary/raw strings and character literals removed; Interpolated strings with quoted expressions are not structurally parsed and may leak apparent references; counts are approximate. Explicit qualified spellings only. Local bare names, aliases, imports and transitive uses are missed; qualified-name collisions are still possible. Not proof dependency or mutant-kill evidence."
    for m in specs:
        if m["id"]=="M24":m["candidate_limitation"]="Basic mulmod literal outputs coincide for product and sum; arithmetic projection is non-discriminating. No Lean test outcome inferred."
    return {"method":"heuristic offset-preserving nested-comment/string/character stripping and explicit qualified token search","lexical_limitations":"Interpolated strings with nested quoted expressions may leak apparent code references; neither tokenizer nor qualified-name search is Lean name resolution","mutants":len(specs),"with_explicit_code_mentions":sum(m["explicit_code_mention_count"]>0 for m in specs),"strong_candidates_updated":sorted(overrides),"semantic_kills":None,"semantic_survivors":None,"boundary":"Candidate existence and source spelling only; no Lean name resolution or elaboration"}
