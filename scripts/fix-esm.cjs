#!/usr/bin/env node
// Fix Agda 2.9.0 ES6 output: add missing `const exports = {};`
// for modules that reference `exports` without defining it.
const fs = require('fs');
const path = require('path');

const buildDir = process.argv[2] || '_build';

const files = fs.readdirSync(buildDir).filter(f => f.endsWith('.mjs'));

let fixed = 0;
for (const file of files) {
  const filePath = path.join(buildDir, file);
  const content = fs.readFileSync(filePath, 'utf8');

  // Skip files that already define exports
  if (content.includes('const exports')) continue;

  // Fix files that reference exports without defining it
  if (content.includes('exports')) {
    // Find last import line
    const lines = content.split('\n');
    let lastImportIdx = -1;
    for (let i = 0; i < lines.length; i++) {
      if (lines[i].startsWith('import ')) lastImportIdx = i;
    }

    if (lastImportIdx >= 0) {
      lines.splice(lastImportIdx + 1, 0, '', 'const exports = {};');
    } else {
      lines.unshift('const exports = {};', '');
    }

    fs.writeFileSync(filePath, lines.join('\n'), 'utf8');
    fixed++;
  }
}

if (fixed > 0) console.log(`Fixed ${fixed} modules (added missing exports)`);
