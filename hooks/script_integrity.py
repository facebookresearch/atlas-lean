"""Pin the scripts the site loads from a CDN to the bytes they had when listed here."""

from __future__ import annotations

from mkdocs.exceptions import PluginError

# Subresource integrity of each external script in mkdocs.yml's extra_javascript.
# A version bump needs a new hash: openssl dgst -sha384 -binary FILE | openssl base64 -A
INTEGRITY = {
    "https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-mml-chtml.js":
        "sha384-Wuix6BuhrWbjDBs24bXrjf4ZQ5aFeFWBuKkFekO2t8xFU0iNaLQfp2K6/1Nxveei",
    "https://cdn.jsdelivr.net/npm/mermaid@11.4.1/dist/mermaid.min.js":
        "sha384-rbtjAdnIQE/aQJGEgXrVUlMibdfTSa4PQju4HDhN3sR2PmaKFzhEafuePsl9H/9I",
}


def on_config(config):
    """Refuse an external script without a pinned hash, so a version bump can't skip one."""
    external = [str(entry) for entry in config.extra_javascript if str(entry).startswith(("http://", "https://"))]
    unpinned = [url for url in external if url not in INTEGRITY]
    if unpinned:
        raise PluginError(f"hooks/script_integrity.py has no integrity hash for {', '.join(unpinned)}")
    return config


def on_post_page(output: str, **_) -> str:
    for url, digest in INTEGRITY.items():
        output = output.replace(f'src="{url}"', f'src="{url}" integrity="{digest}" crossorigin="anonymous"')
    return output
