"""Fetch per-lecture note PDFs from MIT OCW: fetch_ocw_lectures.py WORK

Per book: collect resource slugs from the course's index pages, keep those
matching the book's lecture pattern, and download each resource's PDF into
sources/<Book>/raw/.
"""
import re, sys, urllib.request
from pathlib import Path

PATTERNS = {  # book: (include, exclude) regexes over resource slugs
    'AlgebraicCombinatorics': (r'^(notes\d*|boolean|hadamard|sperner|young)$', r'^hw'),
    'AnAlgorithmistsToolkit': (r'(scribe\d+|spiel_lec\d+)$', r'ps\d|hints'),
    'ArithmeticGeometry': (r'_lec\d+$', r'pset'),
    'BooleanFunctions': (r'_lec[\d\-]+$', r'pset'),
    'CombinatorialOptimization': (r'^l\d+$', r'^a\d'),
    'ComplexVariables': (r'^lecture\d+$', r''),
    'DifferentialGeometry': (r'^ch\d+_revised$', r''),
    'EllipticCurves': (r'_notes\d+$', r'ps|slides|errata'),
    'FourierAnalysis': (r'_(intro|booleanrings|lptheory|orthonormal|fseries\d|fourierint\d|brownian)$', r'pset|mid|final|prac'),
    'GeometryOfManifolds': (r'^lect\d+$', r'homework|sol'),
    'IntroductionToPartialDifferentialEquations': (r'_lec_\d+$', r'problem|exam|final|bonus'),
    'TheoryOfComputation': (r'_lec\d+$', r'hw|mid|final'),
}

def get(url):
    with urllib.request.urlopen(url, timeout=60) as r:
        return r.read()

checkout = Path(__file__).resolve().parents[2]
here = Path(sys.argv[1])
readme = (checkout / 'v1' / 'README.md').read_text()
base = dict(re.findall(r'^\| \[(\w+)\]\((https://ocw\.mit\.edu/courses/[^/)]+)', readme, re.M))
for book, (include, exclude) in PATTERNS.items():
    html = ''
    for page in ('download/', 'pages/lecture-notes/', 'resources/lecture-notes/', 'pages/readings/', 'pages/lecture-slides/'):
        try:
            html += get(f'{base[book]}/{page}').decode('utf-8', 'replace')
        except Exception:
            pass
    slugs = sorted({s for s in re.findall(r'/resources/([a-z0-9_\-]+)/', html)
                    if re.search(include, s) and not (exclude and re.search(exclude, s)) and not s.endswith('-1')})
    raw = here / 'sources' / book / 'raw'
    raw.mkdir(parents=True, exist_ok=True)
    got = 0
    for slug in slugs:
        try:
            page = get(f'{base[book]}/resources/{slug}/').decode('utf-8', 'replace')
            pdf = next(h for h in re.findall(r'href="([^"]+\.pdf)"', page))
            url = pdf if pdf.startswith('http') else 'https://ocw.mit.edu' + pdf
            (raw / f'{slug}.pdf').write_bytes(get(url))
            got += 1
        except Exception as error:
            print(f'  {book}/{slug}: {type(error).__name__}')
    print(f'{book}: {got}/{len(slugs)} lecture PDFs')
