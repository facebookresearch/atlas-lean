"""Convert PDFs to line-citable text: pdf_to_text.py OUT_DIR PDF...

Writes OUT_DIR/<pdf stem>.txt with a '=== page N ===' line before each page.
Math comes out lossy; references such as 'by Theorem 3.2' survive.
"""
import sys
from pathlib import Path
from pypdf import PdfReader

out_dir = Path(sys.argv[1])
out_dir.mkdir(parents=True, exist_ok=True)
for name in sys.argv[2:]:
    reader = PdfReader(name)
    parts = []
    for number, page in enumerate(reader.pages, 1):
        try:
            text = page.extract_text() or ""
        except Exception as error:  # a damaged page should not lose the rest
            text = f"[page text unavailable: {type(error).__name__}]"
        parts.append(f"=== page {number} ===\n{text.strip()}\n")
    target = out_dir / (Path(name).stem + ".txt")
    target.write_text("\n".join(parts), encoding="utf-8")
    print(f"{target.name}: {len(reader.pages)} pages, {sum(p.count(chr(10)) for p in parts)} lines")
