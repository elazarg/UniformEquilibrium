// Node runner for the evaluator self-check: node Games/games/sequencer/tools/run_selftest.js
import { runSelfTest } from "../selftest.js";

const report = runSelfTest();
for (const check of report.checks) {
  console.log(`\n[${check.passed ? "PASS" : "FAIL"}] ${check.name}`);
  for (const [key, value] of Object.entries(check)) {
    if (key === "name" || key === "passed") continue;
    console.log(`    ${key}: ${JSON.stringify(value)}`);
  }
}
console.log(`\noverall: ${report.passed ? "PASS" : "FAIL"}`);
process.exit(report.passed ? 0 : 1);
