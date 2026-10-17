"""Write <work>/sources/<Book>/targets.json from the v1 report: write_targets.py WORK BOOK..."""
import json, sys
from pathlib import Path
checkout = Path(__file__).resolve().parents[2]; here = Path(sys.argv[1])
for book in sys.argv[2:]:
    details = json.loads((checkout / 'v1' / 'Atlas' / book / 'report.json').read_text())['statements']['details']
    rows = [{k: x[k] for k in ('idx', 'kind', 'name', 'location', 'description')} for x in sorted(details, key=lambda x: x['idx'])]
    out = here / 'sources' / book / 'targets.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(rows, indent=1, ensure_ascii=False))
    print(book, len(rows))
