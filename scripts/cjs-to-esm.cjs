#!/usr/bin/env node
// Convert CommonJS Agda output to ES6 modules
const fs = require('fs');
const path = require('path');

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
    /var (z_\w+) = require\("([^"]+)"\);/g,
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

  fs.writeFileSync(outputPath, content, 'utf8');
  converted++;
}

console.log(`Converted ${converted} files`);
