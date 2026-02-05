#!/usr/bin/env node

// generate-anim-data.js — Extract AnimDemo computed values to JSON
//
// Usage:
//   node scripts/generate-anim-data.js <output>
//
// Example:
//   node scripts/generate-anim-data.js examples_html/generated/anim-demo.json

import { writeFileSync, mkdirSync } from 'fs';
import { dirname, resolve } from 'path';
import { pathToFileURL } from 'url';

const output = process.argv[2];
if (!output) {
  console.error('Usage: node scripts/generate-anim-data.js <output>');
  process.exit(1);
}

const buildDir = resolve(process.cwd(), '_build');
const load = name => import(pathToFileURL(`${buildDir}/${name}.mjs`).href).then(m => m.default);

const [Demo, Spring] = await Promise.all([
  load('jAgda.AnimDemo'),
  load('jAgda.Agdelte.Anim.Spring'),
]);

const data = {
  opacityMidValue:   Demo['opacityMidValue'],
  opacityEndValue:   Demo['opacityEndValue'],
  opacityDone:       Demo['opacityDone'],
  retargetedFrom:    Demo['retargetedFrom'],
  linearStart:       Demo['linearStart'],
  dialogPos1:        Demo['dialogPos1'],
  dialogSettled:     Demo['dialogSettled'],
  dialogFinalPos:    Demo['dialogFinalPos'],
  retargetedTarget:  Demo['retargetedTarget'],
  customPos:         Spring['Spring']['position'](Demo['customSpring']),
  customTarget:      Spring['Spring']['target'](Demo['customSpring']),
  customStiffness:   Spring['Spring']['stiffness'](Demo['customSpring']),
  tabTarget:         Spring['Spring']['target'](Demo['tabSpring']),
};

mkdirSync(dirname(resolve(output)), { recursive: true });
writeFileSync(output, JSON.stringify(data, null, 2) + '\n');
console.log(`${output} (${Object.keys(data).length} values)`);
