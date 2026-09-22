"""Check historical and fresh release build evidence without invoking Lean."""
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts/exact_certificate"))
from verify_full_seven_long import source_hashes, TARGETS, parse_axioms

def sha(data): return hashlib.sha256(data).hexdigest()

def lean_tokens(text):
    """Remove nested comments outside strings, then preserve lexical boundaries."""
    result=[];i=0;depth=0
    while i<len(text):
        if depth:
            if text.startswith("/-",i):depth+=1;i+=2
            elif text.startswith("-/",i):depth-=1;i+=2
            else:i+=1
        elif text.startswith("/-",i):
            result.append(" ");depth=1;i+=2
        elif text.startswith("--",i):
            end=text.find("\n",i);i=len(text) if end<0 else end
            result.append(" ")
        elif text[i]=='"':
            start=i;i+=1
            while i<len(text):
                if text[i]=="\\":i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
            result.append(text[start:i])
        else:
            result.append(text[i]);i+=1
    if depth:raise ValueError("Unterminated Lean comment")
    return re.findall(r'"(?:\\.|[^"\\])*"|\w+|[^\w\s]+',"".join(result))

def check_release_build(current):
    folder=ROOT/"certificate/verification/release-20260921"
    for line in (folder/"SHA256SUMS").read_text(encoding="utf-8").splitlines():
        expected,name=line.split("  ",1)
        assert sha((folder/name).read_bytes())==expected,name
    attempt=folder/"attempt-02"
    state=json.loads((attempt/"status.json").read_text(encoding="utf-8"))
    verification=attempt/"verification"
    record=json.loads((verification/"formalization.json").read_text(encoding="utf-8"))
    assert state["status"]==record["status"]=="PASS"
    assert state["release_commit"]==record["source_base_commit"]=="8bf9d8d286bb409ae922393a261b08648b2b6d79"
    assert sha((verification/"formalization.json").read_bytes())==state["formalization_sha256"]
    assert state["all_project_modules_built"] and state["source_files_unchanged"]
    assert state["original_project_started_without_build_cache"]
    assert sha((folder/"status.json").read_bytes())==state["original_attempt_status_sha256"]
    snapshot=folder/"initial-source-hashes.json"
    assert sha(snapshot.read_bytes())==state["original_source_hashes_sha256"]
    sources=json.loads(snapshot.read_text(encoding="utf-8"))
    paths=list((ROOT/"LeanFlagAlgebras").rglob("*.lean"))+[ROOT/"LeanFlagAlgebras.lean"]
    assert set(sources)=={p.relative_to(ROOT).as_posix() for p in paths}
    assert len(sources)==state["project_module_count"]==246
    for name,h in sources.items():
        assert sha((ROOT/name).read_bytes())==h,name
    assert record["repository_source_sha256"]==current
    for name,h in record["verification_inputs_sha256"].items():
        path=ROOT/name
        data=path.read_bytes() if name==record["certificate"] else path.read_text(encoding="utf-8").encode()
        assert sha(data)==h,name
    for stage in state["stages"]:
        assert stage["status"]=="passed" and stage["returncode"]==0,stage["name"]
        assert sha((attempt/(stage["name"]+".log")).read_bytes())==stage["log_sha256"]
    full=next(stage for stage in state["stages"] if stage["name"]=="full-library")
    assert full["command"][-1]=="build"
    assert "Build completed successfully" in (attempt/"full-library.log").read_text(encoding="utf-8")
    for name,h in record["verification_logs_sha256"].items():
        assert sha((verification/name).read_bytes())==h,name
    sweeps=record["sweep_verification"]
    assert sweeps["status"]=="SWEEPS_PASS" and sweeps["scope"]==[0,49]
    covered=[]
    for batch in sweeps["batches"]:
        log=verification/"sweeps"/batch["log"]
        assert sha(log.read_bytes())==batch["log_sha256"]
        assert "Build completed successfully" in log.read_text(encoding="utf-8")
        covered.extend(target for target in batch["targets"] if "Sweep7_" in target)
    assert len(set(covered))==len(covered)==49
    assert sorted(covered)==sorted(record["sweep_targets"])
    actual={k:sorted(v) for k,v in parse_axioms((verification/"lean-axioms.log").read_text(encoding="utf-8")).items()}
    assert actual==record["axioms"] and len(actual)==17
    assert all("sorryAx" not in axioms for axioms in actual.values())
    assert sha((verification/"PinnedHeadline.lean").read_text(encoding="utf-8").encode())==record["pinned_statement_source_sha256"]
    certificate=ROOT/record["certificate"]
    assert sha(certificate.read_bytes())==record["certificate_sha256"]
    assert json.loads(certificate.read_text(encoding="utf-8"))["bound_fraction"]==record["bound_fraction"]
    print(json.dumps(dict(status="release_build_evidence_matches",verified_commit=record["source_base_commit"],
        project_modules=len(sources),coefficient_sweeps=len(covered),completed_utc=state["completed_utc"],
        lean_invoked_by_this_check=False)))

def check():
    if not __debug__:raise SystemExit("Do not run evidence checks with Python optimization enabled.")
    folder=ROOT/"certificate/verification"
    mapping=json.loads((folder/"release-source-map.json").read_text(encoding="utf-8"))
    original=(folder/"formalization.json").read_bytes()
    assert sha(original)==mapping["historical_record_sha256"]
    record=json.loads(original);assert record["status"]=="PASS"
    sources=gzip.decompress((folder/"historical-sources.json.gz").read_bytes())
    assert sha(sources)==mapping["historical_sources_sha256"]
    sources=json.loads(sources)
    for module,h in record["repository_source_sha256"].items():
        assert sha(sources[module].encode())==h,module
    current=source_hashes(TARGETS)
    assert set(current)==set(mapping["release_modules"])
    for module,h in current.items():
        row=mapping["release_modules"][module]
        assert h==row["release_sha256"],module
        text=(ROOT/(module.replace(".","/")+".lean")).read_text(encoding="utf-8")
        assert lean_tokens(text)==lean_tokens(sources[module]),module
        assert row["historical_sha256"]==record["repository_source_sha256"][module]
    for name,h in record["verification_logs_sha256"].items():
        assert sha((folder/name).read_bytes())==h,name
    for name,h in mapping["additional_record_sha256"].items():
        assert sha((folder/name).read_bytes())==h,name
    actual={k:sorted(v) for k,v in parse_axioms((folder/"lean-axioms.log").read_text(encoding="utf-8")).items()}
    assert actual=={k:sorted(v) for k,v in record["axioms"].items()}
    cert=json.loads((ROOT/"certificate/K4_turan_order7_certificate.json").read_text(encoding="utf-8"))
    assert cert["bound_fraction"]==record["bound_fraction"]
    assert sha((ROOT/"certificate/K4_turan_order7_certificate.json").read_bytes())==mapping["release_certificate_sha256"]
    for name,h in mapping["build_configuration_sha256"].items():
        assert sha((ROOT/name).read_text(encoding="utf-8").encode())==h
    print(json.dumps(dict(status="historical_evidence_matches",release_modules=len(current),
        historical_modules=len(sources),historical_completed_utc=record["completed_utc"],
        fresh_lean_build=False)))
    check_release_build(current)

if __name__=="__main__":check()
