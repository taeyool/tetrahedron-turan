"""Read, extract and audit the compressed historical experiment evidence."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
from fractions import Fraction

HERE=Path(__file__).resolve().parent
ARCHIVE=HERE/"evidence"
def digest(data):return hashlib.sha256(data).hexdigest()
def key(path):return path.replace("<repo>","").lstrip("\\/").replace("\\","/")
def read_manifest():return json.loads((ARCHIVE/"manifest.json").read_text(encoding="utf-8"))
def read_object(manifest,sha):
    chunks=[]
    obj=manifest["objects"][sha]
    for part in obj["parts"]:
        path=(ARCHIVE/part["path"]).resolve()
        if ARCHIVE.resolve() not in path.parents:raise ValueError("Unsafe archive path")
        raw=path.read_bytes()
        if len(raw)!=part["bytes"] or digest(raw)!=part["sha256"]:raise ValueError(f"Corrupt archive part: {path}")
        chunks.append(raw)
    data=gzip.decompress(b"".join(chunks))
    if len(data)!=obj["bytes"] or digest(data)!=sha:raise ValueError(f"Corrupt object: {sha}")
    return data
def read_file(manifest,path):
    return read_object(manifest,manifest["files"][key(path)]["sha256"])
def check(manifest):
    if not __debug__:raise SystemExit("Do not run evidence checks with Python optimization enabled.")
    for sha in manifest["objects"]:read_object(manifest,sha)
    for path,entry in manifest["files"].items():
        assert entry["sha256"] in manifest["objects"],path
        if "reported_sha256" in entry:
            assert entry["original_sha256"]==entry["reported_sha256"],path
    results=json.loads((HERE/"results_complete_20260913/results.json").read_text(encoding="utf-8"))
    unique={key(r["run_path"]):r for r in results["main_runs"]+results["new_runs"]}
    assert len(unique)==43 and len(results["main_runs"])==39
    assert {r["path"] for r in manifest["runs"]}==set(unique)
    for run in unique.values():
        cert=json.loads(read_file(manifest,run["certificate_path"]))
        assert Fraction(cert["bound_fraction"])==Fraction(run["exact_bound_fraction"])
        assert manifest["files"][key(run["certificate_path"])]["original_sha256"]==run["certificate_sha256"]
    for run in manifest["runs"]:
        row=unique[run["path"]]
        cert=json.loads(read_file(manifest,run["uncompressed_certificate"]))
        assert Fraction(cert["bound_fraction"])==Fraction(row["uncompressed_bound_fraction"])
    checked=0
    assert len(manifest["checkpoints"])==len(results["checkpoints"])
    for row,archived in zip(results["checkpoints"],manifest["checkpoints"]):
        assert archived["status"]==row["status"]
        if row["status"]=="verified":
            cert=json.loads(read_file(manifest,archived["certificate"]))
            assert Fraction(cert["bound_fraction"])==Fraction(row["bound_fraction"] if "bound_fraction" in row else row["exact_bound_fraction"])
            if row.get("certificate_sha256"):
                assert manifest["files"][archived["certificate"]]["original_sha256"]==row["certificate_sha256"]
            checked+=1
    assert not manifest["unavailable_source_versions"]
    for row in manifest["source_versions"]:
        assert manifest["files"][row["entry"]]["original_sha256"]==row["original_sha256"]
    print(json.dumps(dict(status="archive_integrity_and_report_links_pass",runs=len(unique),
        checkpoint_certificates=checked,files=len(manifest["files"]),objects=len(manifest["objects"]),
        historical_source_versions=len(manifest["source_versions"]),
        note="Hash and report-link checks; not a fresh exhaustive coefficient scan or Lean build.")))
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--check",action="store_true")
    p.add_argument("--list",action="store_true")
    p.add_argument("--extract",help="Historical path from results.json, or source entry from manifest.json")
    p.add_argument("--output",type=Path)
    a=p.parse_args();m=read_manifest()
    if a.check:check(m)
    if a.list:print(json.dumps(m["runs"],indent=2))
    if a.extract:
        if a.output is None:p.error("--extract requires --output")
        data=read_file(m,a.extract)
        a.output.parent.mkdir(parents=True,exist_ok=True)
        with a.output.open("xb") as stream:stream.write(data)
        print(json.dumps(dict(extracted=str(a.output),sha256=digest(data))))
    if not(a.check or a.list or a.extract):p.print_help()
if __name__=="__main__":main()
