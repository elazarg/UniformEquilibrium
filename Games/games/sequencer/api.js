// Portal API client for the sequencer.
//
// Everything that ends up in the ledger goes through here.  The in-browser
// evaluator drives feel; these calls decide what is actually recorded, and
// mock mode records nothing at all.

import { MOCK_CURATED, MOCK_CANDIDATES } from "./mockdata.js";
import { evaluate } from "./evaluator.js";

export const QUERY = new URLSearchParams(window.location.search);
export const MOCK = QUERY.get("mock") === "1";

export class ApiError extends Error {
  constructor(kind, message, status = 0) {
    super(message);
    this.kind = kind; // "offline" | "unavailable" | "server" | "bad-request"
    this.status = status;
  }
}

async function request(method, path, body) {
  if (MOCK) return mockRequest(method, path, body);
  let response;
  try {
    response = await fetch(path, {
      method,
      headers: body ? { "Content-Type": "application/json" } : undefined,
      body: body ? JSON.stringify(body) : undefined,
    });
  } catch (error) {
    throw new ApiError("offline", `cannot reach the portal server (${error.message})`);
  }
  if (response.status === 503) {
    throw new ApiError("unavailable", "the portal server is busy or starting up", 503);
  }
  let payload = null;
  const text = await response.text();
  if (text) {
    try {
      payload = JSON.parse(text);
    } catch {
      throw new ApiError("server", `malformed response from ${path}`, response.status);
    }
  }
  if (!response.ok) {
    const detail = payload && payload.error ? payload.error : `HTTP ${response.status}`;
    const kind = response.status >= 500 ? "server" : "bad-request";
    throw new ApiError(kind, detail, response.status);
  }
  return payload;
}

// Mock mode answers in the documented shapes so the whole UI can be driven
// offline.  The evaluate response is the local evaluator's own output, which
// is exactly why mock results are labelled as unrecorded everywhere they show.
function mockRequest(method, path, body) {
  const delay = (value) => new Promise((done) => setTimeout(() => done(value), 90));
  if (method === "GET" && path.startsWith("/api/tables/curated")) {
    return delay({ tables: MOCK_CURATED });
  }
  if (method === "GET" && path.startsWith("/api/candidates")) {
    return delay({ candidates: MOCK_CANDIDATES });
  }
  if (method === "GET" && path.startsWith("/api/stats")) {
    return delay({
      candidates: MOCK_CANDIDATES.length,
      best_score: 0.0301031043470954,
      library_profiles: 0,
      kills: 0,
      games: ["sequencer"],
    });
  }
  if (method === "POST" && path === "/api/evaluate") {
    const report = evaluate(body.table, body.profile.hazards);
    return delay({
      exploitability: report.exploitability,
      per_player: report.per_player,
      on_path: report.on_path,
      best_deviations: report.best_deviations.map((d) => ({
        player: d.player,
        value: d.value,
        policy: d.policy,
      })),
      mock: true,
    });
  }
  if (method === "POST" && path === "/api/candidates") {
    return delay({
      id: `mock-candidate-${Date.now().toString(36)}`,
      record: {
        status: "proposed",
        tier: "survivor-standard",
        evaluation: { score: null, level: "standard" },
      },
      mock: true,
    });
  }
  if (method === "POST" && path === "/api/profiles") {
    return delay({ id: `mock-profile-${Date.now().toString(36)}`, mock: true });
  }
  if (method === "POST" && path === "/api/harden") {
    // Same shape and the same smallest-denominator-first search as the engine,
    // but the arithmetic here is the browser's float evaluator, so mock mode
    // can exercise the flow without ever claiming the exact tier for real.
    const denominators = [2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 25, 32, 50, 64, 100];
    const attempts = [];
    let winner = null;
    let best = null;
    for (const denominator of denominators) {
      const hazards = body.profile.hazards.map((row) =>
        row.map((value) => Math.min(1, Math.max(0, Math.round(value * denominator) / denominator))),
      );
      const value = evaluate(body.table, hazards).exploitability;
      const attempt = {
        denominator,
        profile: { period: hazards.length, hazards },
        exploitability: value,
        exploitability_exact: null,
        kills: value <= 0.02,
      };
      attempts.push(attempt);
      if (best === null || value < best.exploitability) best = attempt;
      if (attempt.kills) {
        winner = attempt;
        break;
      }
    }
    const chosen = winner || best;
    return delay({
      kills: Boolean(winner),
      eps_kill: 0.02,
      tier: winner ? "exact" : null,
      denominator: chosen.denominator,
      profile: chosen.profile,
      hazards_exact: null,
      exploitability: chosen.exploitability,
      exploitability_exact: null,
      attempts,
      claim:
        "Mock mode: this snap was re-evaluated in floating point, not in exact " +
        "rational arithmetic, so it is not evidence of the exact tier.",
      mock: true,
    });
  }
  throw new ApiError("bad-request", `unmocked route ${method} ${path}`, 404);
}

export const api = {
  curated: () => request("GET", "/api/tables/curated"),
  candidates: (limit = 50) => request("GET", `/api/candidates?limit=${limit}`),
  proposeCandidate: (table, session, provenance) =>
    request("POST", "/api/candidates", {
      table,
      game: "sequencer",
      session,
      provenance,
    }),
  stats: () => request("GET", "/api/stats"),
  evaluate: (table, profile) => request("POST", "/api/evaluate", { table, profile }),
  submitProfile: (profile, source) =>
    request("POST", "/api/profiles", { profile, source }),
  // Rational snap: small-denominator hazards re-verified in exact arithmetic.
  // A server without the route is handled by the caller as a plain submission.
  harden: (table, profile) => request("POST", "/api/harden", { table, profile }),
};
