// Build bridge: one batch over stdin keeps the handbook generator deterministic.
import { highlightLim } from '../docs/lim-highlight.mjs';
let input = '';
for await (const chunk of process.stdin) input += chunk;
process.stdout.write(JSON.stringify(JSON.parse(input).map(highlightLim)));
