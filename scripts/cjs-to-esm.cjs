#!/usr/bin/env node
// Convert CommonJS Agda output to ES6 modules
const fs = require('fs');
const path = require('path');

// Base64 VLQ encoding for source maps
function encodeVLQ(value) {
  let vlq = value < 0 ? ((-value) << 1) + 1 : value << 1;
  let encoded = '';
  const B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';
  do {
    let digit = vlq & 0x1f;
    vlq >>>= 5;
    if (vlq > 0) digit |= 0x20;
    encoded += B64[digit];
  } while (vlq > 0);
  return encoded;
}

// Generate a simple line-by-line identity source map
function generateSourceMap(sourceFile, outputFile, inputLineCount, outputLineCount) {
  const mappings = [];
  // Track state for relative VLQ encoding
  let prevSourceLine = 0;
  for (let i = 0; i < outputLineCount; i++) {
    // Map each output line col 0 -> source file 0, source line i, col 0
    // Since the transform is mostly 1:1, map output line i to input line i
    // (clamped to input line count)
    const sourceLine = Math.min(i, inputLineCount - 1);
    // Each segment: [outCol, srcFileIdx, srcLine, srcCol]
    // All relative to previous values; outCol resets per line
    const outCol = encodeVLQ(0);           // column 0 (resets each line)
    const srcFile = encodeVLQ(0);          // always file index 0
    const srcLine = encodeVLQ(sourceLine - prevSourceLine);
    const srcCol = encodeVLQ(0);           // column 0
    prevSourceLine = sourceLine;
    mappings.push(outCol + srcFile + srcLine + srcCol);
  }
  return JSON.stringify({
    version: 3,
    file: path.basename(outputFile),
    sources: [path.basename(sourceFile)],
    sourcesContent: [null],
    mappings: mappings.join(';')
  });
}

const buildDir = process.argv[2] || '_build/2.9.0';
const targetDir = process.argv[3] || '_build';

console.log(`Converting ${buildDir}/*.js to ${targetDir}/*.mjs`);

const files = fs.readdirSync(buildDir).filter(f => f.endsWith('.js'));

let converted = 0;
for (const file of files) {
  const inputPath = path.join(buildDir, file);
  const outputPath = path.join(targetDir, file.replace('.js', '.mjs'));

  let content = fs.readFileSync(inputPath, 'utf8');

  // Convert require("agda-rts") to import
  content = content.replace(
    /var agdaRTS = require\("agda-rts"\);/g,
    'import agdaRTS from "./agda-rts.mjs";'
  );

  // Convert var x = require("y"); to import x from "./y.mjs";
  content = content.replace(
    /var (\w+) = require\("([^"]+)"\);/g,
    'import $1  from "./$2.mjs";'
  );

  // Add const exports = {}; after imports if file uses exports
  if (content.includes('exports.') || content.includes('exports[')) {
    // Split into lines, find last import, insert after it
    const lines = content.split('\n');
    let lastImportIdx = -1;

    for (let i = 0; i < lines.length; i++) {
      if (lines[i].startsWith('import ')) {
        lastImportIdx = i;
      }
    }

    if (lastImportIdx >= 0) {
      // Insert blank line and const exports after last import
      lines.splice(lastImportIdx + 1, 0, '', 'const exports = {};');
      content = lines.join('\n');
    } else {
      // No imports, add at the beginning
      content = 'const exports = {};\n\n' + content;
    }
  }

  // Add export default exports at the end if not present
  if (!content.includes('export default exports')) {
    content += '\n;export default exports;\n';
  }

  // Generate and append source map
  const inputLineCount = fs.readFileSync(inputPath, 'utf8').split('\n').length;
  const outputLineCount = content.split('\n').length;
  const mapFileName = path.basename(outputPath) + '.map';
  const sourceMap = generateSourceMap(file, outputPath, inputLineCount, outputLineCount);

  content += '//# sourceMappingURL=' + mapFileName + '\n';

  fs.writeFileSync(outputPath, content, 'utf8');
  fs.writeFileSync(outputPath + '.map', sourceMap, 'utf8');
  converted++;
}

console.log(`Converted ${converted} files`);
