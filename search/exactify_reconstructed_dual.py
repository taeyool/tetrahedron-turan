"""Exact conversion for M7-no5 and M7-lift6, with both exhaustive scans.

Compatibility entry point used by the historical campaign supervisors. The
shared verifier already supports the twelve original blocks and no five-root
blocks. Lifted M6 duals must first be padded with three empty factor matrices,
as in experiments/run_remaining_campaign.py.
"""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import numpy as np
from exactify_five_root import main as verify_main, BASE_DIMS

def main():
    if "--types" not in sys.argv and "--certificate" not in sys.argv:
        sys.argv += ["--types", ""]
    if "--scale" not in sys.argv:
        sys.argv += ["--scale", "1000000"]
    if "--cross-check-pricing" not in sys.argv:
        sys.argv.append("--cross-check-pricing")
    # The lifted runner declares its nine active blocks and already stores the
    # three additional empty factor matrices. Validate that representation
    # before adapting only its dimension metadata to the shared verifier.
    source = Path(sys.argv[1]) if len(sys.argv)>1 and not sys.argv[1].startswith("-") else None
    if source is None:
        verify_main()
        return
    with np.load(source, allow_pickle=False) as z:
        lifted = "dimensions" in z and len(z["dimensions"]) == 9
        if not lifted:
            verify_main()
            return
        if str(z["model"]) != "M7-lift6" or list(z["dimensions"]) != BASE_DIMS[:9]:
            raise ValueError("Unexpected nine-block dual")
        for i,d in enumerate(BASE_DIMS[9:],9):
            if z[f"factors{i}"].shape != (0,d) or np.any(z[f"gram{i-9}"]):
                raise ValueError("Lifted dual has nonzero added blocks")
        values = {k:z[k] for k in z.files}
    values["dimensions"] = np.asarray(BASE_DIMS)
    cache = Path(sys.argv[sys.argv.index("--cache")+1])
    cache.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="lift-metadata-",dir=cache) as tmp:
        normalized = Path(tmp)/"dual.npz"
        np.savez(normalized,**values)
        sys.argv[1] = str(normalized)
        verify_main()
    output = Path(sys.argv[sys.argv.index("--output")+1])
    cert = json.loads(output.read_text(encoding="utf-8"))
    cert["reconstruction"].update(source_dual=str(source),
        source_dual_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        dimension_metadata_note="Nine active lifted blocks; three explicitly empty blocks validated and declared for the shared verifier.")
    output.write_text(json.dumps(cert,indent=2)+"\n",encoding="utf-8")

if __name__ == "__main__":
    main()
