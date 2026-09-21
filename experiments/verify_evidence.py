"""Independently verify an extracted M6 or M7 integer certificate."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import runtime as rt

def main():
    if not __debug__:raise SystemExit("Do not run certificate verification with Python optimization enabled.")
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--certificate",type=Path,required=True)
    p.add_argument("--cache",type=Path,required=True)
    p.add_argument("--output",type=Path,required=True)
    a=p.parse_args()
    cert=json.loads(a.certificate.read_text(encoding="utf-8"))
    if cert.get("model")=="M6":
        if not (a.cache/"components.npz").exists():
            subprocess.run([sys.executable,"-X","utf8",str(rt.HERE/"runtime.py"),
                            str(rt.RESEARCH/"analyze_certificate.py"),"--cache",str(a.cache),
                            "--output",str(a.cache/"diagnostics.json")],check=True)
        from remaining_models import prepare
        from exactify_order6 import verify
        if not (a.cache/"order6-independent.npz").exists():prepare(a.cache)
        result=verify(cert,a.cache)
        rt.write_json(a.output,result)
        print(json.dumps(result))
    else:
        subprocess.run([sys.executable,"-X","utf8",str(rt.HERE/"runtime.py"),
                        str(rt.RESEARCH/"exactify_five_root.py"),"--certificate",str(a.certificate),
                        "--cache",str(a.cache),"--output",str(a.output),
                        "--cross-check-pricing","--threads","2"],check=True)

if __name__=="__main__":main()
