"""Keep Material's eager browser search index proportional to page count."""

from __future__ import annotations

import json
from pathlib import Path

from mkdocs.plugins import event_priority


@event_priority(-100)
def on_post_build(*, config) -> None:
    """Discard section and body records after Material writes its index."""

    index = Path(config.site_dir) / "search" / "search_index.json"
    payload = json.loads(index.read_text(encoding="utf-8"))
    documents = payload.get("docs")
    if not isinstance(documents, list):
        raise TypeError("Material search index has no document list")

    pages: list[dict[str, object]] = []
    seen: set[str] = set()
    for document in documents:
        if not isinstance(document, dict):
            raise TypeError("Material search index contains a non-object document")
        location = document.get("location")
        if not isinstance(location, str):
            raise TypeError("Material search document has no string location")
        if "#" in location or location in seen:
            continue
        page = {key: value for key, value in document.items() if key not in {"parent", "text"}}
        page["text"] = ""
        pages.append(page)
        seen.add(location)

    payload["docs"] = pages
    index.write_text(
        json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
