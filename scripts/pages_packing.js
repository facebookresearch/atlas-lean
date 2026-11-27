// Opens the pages that the GitHub Pages copy of the site stores gzipped: the pages under mathlib/ and roadmap/
// (scripts/pack_pages_site.py, docs/BLUEPRINT.md). GitHub Pages serves a stored .gz file as application/gzip,
// without Content-Encoding, so the browser does not inflate it. The site serves this script as
// javascripts/pages-packing.js.
//
// - At the address of each stored page, a small page loads this script with the stored file's name in
//   data-packed-page: the script fetches it, inflates it with DecompressionStream and opens it in place of the
//   small page.
// - The explorer and the project map fetch the pages they show. Every page that runs either loads this script
//   first, and the script answers a fetch of a stored page with the inflated page. The answer has no URL of its own,
//   so the explorer reads the page as the one it asked for. Every other request goes to the browser's fetch as it
//   came, unread.
(function () {
  "use strict";
  var script = document.currentScript;
  if (!script) return;
  var root = new URL("..", script.src);
  var stored = script.getAttribute("data-packed-page");
  var inflates = typeof window.fetch === "function" && typeof DecompressionStream === "function";

  function inflated(response) {
    return response.body.pipeThrough(new DecompressionStream("gzip"));
  }

  // The same rule as pack_pages_site.py's is_packed, on a path below the site's root.
  function isPacked(path) {
    return /^(?:mathlib|roadmap)\/.+\.html$/.test(path);
  }

  if (inflates && !window.fetch.pagesPacking) {
    var fetch = window.fetch;
    var packed = function (input, init) {
      // Tell a fetch of a stored page from the rest without reading the request, so that a request with a body
      // reaches the browser's fetch untouched.
      var url, method, path;
      try {
        url = new URL(input instanceof Request ? input.url : String(input), document.baseURI);
        method = String((init && init.method) || (input instanceof Request ? input.method : "GET")).toUpperCase();
      } catch (error) {
        return fetch.apply(window, arguments);
      }
      path = url.pathname.slice(root.pathname.length);
      if (/\/$/.test(path)) path += "index.html";
      if (method !== "GET" || url.origin !== root.origin || url.pathname.indexOf(root.pathname) !== 0 ||
          !isPacked(path)) {
        return fetch.apply(window, arguments);
      }
      var file = new URL(root.href);
      file.pathname = root.pathname + path + ".gz";
      file.search = url.search;
      // A stored page is a file: it is never redirected, and a redirect could lead outside the site.
      var request;
      try {
        var asked = new Request(input instanceof Request ? input : url.href, init);
        request = new Request(new Request(file.href, asked), {redirect: "error"});
      } catch (error) {
        return fetch.apply(window, arguments);
      }
      return fetch.call(window, request).then(function (response) {
        if (!response.ok) return response;
        return new Response(inflated(response), {headers: {"Content-Type": "text/html; charset=utf-8"}});
      });
    };
    packed.pagesPacking = true;
    window.fetch = packed;
  }

  if (!stored) return;

  // The small page's note, made visible at once and saying what went wrong.
  function show(message) {
    var write = function () {
      var note = document.querySelector("p") || document.body.appendChild(document.createElement("p"));
      note.textContent = message;
      note.style.animation = "none";
      note.style.visibility = "visible";
    };
    if (document.body) write(); else document.addEventListener("DOMContentLoaded", write);
  }

  if (!inflates) {
    show("This page is stored compressed, and this browser cannot open it: it lacks fetch or DecompressionStream.");
    return;
  }
  var address = new URL(stored, location.href).href;
  window.fetch(address, {credentials: "same-origin", redirect: "error"}).then(function (response) {
    if (!response.ok) throw new Error("HTTP " + response.status);
    return new Response(inflated(response)).text();
  }).then(function (page) {
    var anchor = "";
    try { anchor = decodeURIComponent(location.hash.slice(1)); } catch (error) { anchor = ""; }
    document.open();
    document.write(page);
    document.close();
    // The browser looked for the address's anchor before the page existed.
    if (anchor) {
      window.addEventListener("load", function () {
        var target = document.getElementById(anchor);
        if (target) target.scrollIntoView();
      });
    }
  }).catch(function (error) {
    show("This page is stored compressed and could not be opened: " + error.message + ".");
  });
})();
