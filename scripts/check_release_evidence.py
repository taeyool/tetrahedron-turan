"""Check the historical Lean evidence and its mapping to the release, without Lean."""
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

if __name__=="__main__":check()
