#!/usr/bin/env node
"use strict";

const fs = require("fs");
const katex = require("katex");

function decodeHtml(text) {
  return text
    .replace(/&amp;/g, "&")
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"')
    .replace(/&#39;|&apos;/g, "'")
    .replace(/&#(\d+);/g, (_, value) => String.fromCodePoint(Number(value)))
    .replace(/&#x([0-9a-f]+);/gi, (_, value) =>
      String.fromCodePoint(Number.parseInt(value, 16)),
    );
}

if (process.argv.length < 3) {
  throw new Error("usage: check_katex.cjs HTML...");
}

for (const path of process.argv.slice(2)) {
  const html = fs.readFileSync(path, "utf8");
  const math = /<span class="math (inline|display)">([\s\S]*?)<\/span>/g;
  let match;
  let count = 0;
  while ((match = math.exec(html)) !== null) {
    katex.renderToString(decodeHtml(match[2]), {
      displayMode: match[1] === "display",
      throwOnError: true,
      strict: "error",
    });
    count += 1;
  }
  if (count === 0) {
    throw new Error(`${path}: no Pandoc math spans found`);
  }
  console.log(`${path}: KaTeX ${katex.version} rendered ${count} math fragments`);
}
