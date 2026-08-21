/* Exploit Floor — portal, v3 (full diegesis)
 * - Builds the atlas tile's fog-reveal cell grid (the atlas game's own
 *   parchment rebuild mirrors this exact material — see its style.css).
 * - Wires per-tile info overlays (plain-English pitches, no domain words)
 *   and "the ledger" modal (all one click).
 * - Polls GET /api/stats and GET /api/candidates?limit=10:
 *   - the wall strip gets a single scrolling line of in-fiction events,
 *     built from game+tier only — no numbers, no domain vocabulary;
 *   - the ledger modal gets the real counters, tier legend, honesty
 *     paragraph, and a list of recent records (raw data is fine there,
 *     it's the one out-of-fiction door).
 * - Degrades to a quiet in-fiction line / greyed ledger values on fetch
 *   failure or non-2xx (503 included).
 * - ?mock=1 drives all of the above from canned contract-shaped data
 *   instead of the network, with a small "MOCK DATA" badge.
 */
(function () {
  "use strict";

  var POLL_MS = 5000;
  var MOCK = new URLSearchParams(window.location.search).get("mock") === "1";

  // ---------- atlas fog-reveal grid ----------

  (function buildAtlasScene() {
    var host = document.getElementById("atlas-scene");
    if (!host) return;
    var palette = ["#3a5670", "#7a5327", "#54633c", "#5c4632", "#3a2f22"];
    var cols = 8, rows = 6;
    for (var i = 0; i < cols * rows; i++) {
      var cell = document.createElement("div");
      cell.className = "atlas-cell";
      var delay = ((i * 37) % 280) / 40; // spread reveals across the loop
      var color = palette[i % palette.length];
      cell.style.setProperty("--cell-delay", delay.toFixed(2) + "s");
      cell.style.setProperty("--cell-color", color);
      host.insertBefore(cell, host.firstChild);
    }
  })();

  // ---------- per-tile info overlays (one click to open, one click to close) ----------

  document.querySelectorAll(".info-affordance").forEach(function (btn) {
    btn.addEventListener("click", function (ev) {
      ev.preventDefault();
      var tile = btn.closest(".tile");
      if (!tile) return;
      tile.classList.toggle("info-open");
    });
  });

  document.querySelectorAll(".info-overlay").forEach(function (panel) {
    panel.addEventListener("click", function () {
      var tile = panel.closest(".tile");
      if (tile) tile.classList.remove("info-open");
    });
  });

  // ---------- the ledger (one dedicated out-of-fiction affordance) ----------

  var modalBackdrop = document.getElementById("modal-backdrop");
  var ledgerBtn = document.getElementById("ledger-btn");
  var modalClose = document.getElementById("modal-close");

  function openModal() { modalBackdrop.hidden = false; }
  function closeModal() { modalBackdrop.hidden = true; }

  if (ledgerBtn) ledgerBtn.addEventListener("click", openModal);
  if (modalClose) modalClose.addEventListener("click", closeModal);
  if (modalBackdrop) {
    modalBackdrop.addEventListener("click", function (ev) {
      if (ev.target === modalBackdrop) closeModal();
    });
  }

  document.addEventListener("keydown", function (ev) {
    if (ev.key !== "Escape") return;
    closeModal();
    document.querySelectorAll(".tile.info-open").forEach(function (t) {
      t.classList.remove("info-open");
    });
  });

  // ---------- mock data ----------

  var MOCK_GAMES = ["standoff", "sequencer", "breeder", "atlas"];
  var MOCK_TIERS = [
    "unattacked", "survivor-quick", "survivor-standard", "survivor-deep",
    "numerical-narrow", "numerical-wide", "exact"
  ];

  var mockState = {
    candidates: 187,
    kills: 152,
    library_profiles: 34,
    best_score: 0.0431,
    tick: 0
  };

  function mockCandidateRow(i, ageSeconds) {
    var game = MOCK_GAMES[(i * 7 + mockState.tick) % MOCK_GAMES.length];
    var tier = MOCK_TIERS[(i * 3 + mockState.tick) % MOCK_TIERS.length];
    var score = (0.005 + ((i * 13 + mockState.tick * 5) % 97) / 1000).toFixed(4);
    var created = new Date(Date.now() - ageSeconds * 1000).toISOString();
    return {
      id: "mock-" + i,
      created: created,
      game: game,
      tier: tier,
      evaluation: { score: Number(score) }
    };
  }

  function mockStats() {
    return {
      candidates: mockState.candidates,
      best_score: mockState.best_score,
      library_profiles: mockState.library_profiles,
      kills: mockState.kills,
      games: MOCK_GAMES
    };
  }

  function mockCandidates(limit) {
    var rows = [];
    var ages = [40, 210, 900, 2200, 5400, 9000, 26000, 61000, 130000, 400000];
    for (var i = 0; i < limit && i < ages.length; i++) {
      rows.push(mockCandidateRow(i, ages[i]));
    }
    return { candidates: rows };
  }

  function advanceMock() {
    mockState.tick += 1;
    mockState.candidates += (mockState.tick % 2 === 0) ? 1 : 0;
    if (mockState.tick % 3 === 0) mockState.kills += 1;
  }

  // ---------- fetch helpers ----------

  function fetchJSON(url) {
    return fetch(url, { headers: { Accept: "application/json" } }).then(function (res) {
      if (!res.ok) {
        var err = new Error("HTTP " + res.status);
        err.status = res.status;
        throw err;
      }
      return res.json();
    });
  }

  function getStats() {
    if (MOCK) return Promise.resolve(mockStats());
    return fetchJSON("/api/stats");
  }

  function getCandidates(limit) {
    if (MOCK) return Promise.resolve(mockCandidates(limit));
    return fetchJSON("/api/candidates?limit=" + limit);
  }

  // ---------- formatting (ledger only — raw values are fine there) ----------

  function formatAge(iso) {
    var then = Date.parse(iso);
    if (isNaN(then)) return "—";
    var deltaS = Math.max(0, (Date.now() - then) / 1000);
    if (deltaS < 60) return "just now";
    var m = deltaS / 60;
    if (m < 60) return Math.floor(m) + "m ago";
    var h = m / 60;
    if (h < 24) return Math.floor(h) + "h ago";
    var d = h / 24;
    return Math.floor(d) + "d ago";
  }

  function formatScore(n) {
    if (typeof n !== "number" || isNaN(n)) return "—";
    if (n >= 1e9) return "n/a"; // sentinel for "nothing found by this attack"
    return n.toFixed(4);
  }

  function formatCount(n) {
    if (typeof n !== "number" || isNaN(n)) return "—";
    return String(n);
  }

  // ---------- ledger: stat counters ----------

  var ledgerStatEls = {};
  document.querySelectorAll(".ledger-stat[data-stat]").forEach(function (el) {
    ledgerStatEls[el.getAttribute("data-stat")] = el;
  });

  function setStatOffline(key) {
    var el = ledgerStatEls[key];
    if (!el) return;
    el.classList.add("offline");
    var v = el.querySelector(".ls-value");
    v.textContent = "—";
    v.classList.add("placeholder");
  }

  function setStatValue(key, text) {
    var el = ledgerStatEls[key];
    if (!el) return;
    el.classList.remove("offline");
    var v = el.querySelector(".ls-value");
    v.textContent = text;
    v.classList.remove("placeholder");
  }

  function renderLedgerStats(stats) {
    setStatValue("candidates", formatCount(stats.candidates));
    setStatValue("kills", formatCount(stats.kills));
    setStatValue("library_profiles", formatCount(stats.library_profiles));
    setStatValue("best_score", formatScore(stats.best_score));
  }

  function renderLedgerStatsOffline() {
    setStatOffline("candidates");
    setStatOffline("kills");
    setStatOffline("library_profiles");
    setStatOffline("best_score");
  }

  // ---------- ledger: recent records list ----------

  var ledgerRecords = document.getElementById("ledger-records");

  function renderLedgerRecords(records) {
    ledgerRecords.innerHTML = "";
    if (!records || records.length === 0) {
      var empty = document.createElement("li");
      empty.className = "ledger-record empty";
      empty.innerHTML = '<a href="#" tabindex="-1">no records yet</a>';
      ledgerRecords.appendChild(empty);
      return;
    }
    records.forEach(function (rec) {
      var li = document.createElement("li");
      li.className = "ledger-record";
      var a = document.createElement("a");
      a.href = "/" + (rec.game || "") + "/";

      var game = document.createElement("span");
      game.className = "lr-game";
      game.textContent = rec.game || "—";
      a.appendChild(game);

      var tier = document.createElement("span");
      var tierName = rec.tier || "unknown";
      tier.className = "tier-badge tier-" + tierName.toLowerCase();
      tier.textContent = tierName;
      a.appendChild(tier);

      var score = document.createElement("span");
      score.className = "lr-score";
      var scoreVal = rec.evaluation && typeof rec.evaluation.score === "number"
        ? rec.evaluation.score
        : null;
      score.textContent = scoreVal === null ? "—" : formatScore(scoreVal);
      a.appendChild(score);

      var age = document.createElement("span");
      age.className = "lr-age";
      age.textContent = formatAge(rec.created);
      a.appendChild(age);

      li.appendChild(a);
      ledgerRecords.appendChild(li);
    });
  }

  function renderLedgerRecordsOffline() {
    ledgerRecords.innerHTML = "";
    var li = document.createElement("li");
    li.className = "ledger-record placeholder";
    li.innerHTML = '<a href="#" tabindex="-1">no connection</a>';
    ledgerRecords.appendChild(li);
  }

  // ---------- wall strip: in-fiction ambient feed (no domain words, no numbers) ----------

  var FEED_PHRASES = {
    standoff: {
      killed: [
        "a rigged table finally went down out in Ashfield.",
        "somebody's table didn't make it through the night."
      ],
      survivor: [
        "another rig walked out of Ashfield still standing.",
        "the table held through one more round of gunfire."
      ]
    },
    sequencer: {
      killed: [
        "a groove locked in the back room.",
        "the machine finally found its beat."
      ],
      survivor: [
        "the machine's still hunting for the beat.",
        "a pattern almost locked, then slipped away."
      ]
    },
    breeder: {
      killed: [
        "a sly specimen finally proved its worth.",
        "something clever hatched in the terrarium."
      ],
      survivor: [
        "a fresh brood is growing in the terrarium.",
        "a new specimen reached the lab."
      ]
    },
    atlas: {
      killed: [
        "a patch of the map went dark.",
        "the surveyors marked new ground."
      ],
      survivor: [
        "pale country still holds out on the atlas.",
        "fresh territory got charted."
      ]
    }
  };

  var KILLED_TIERS = { "numerical-narrow": 1, "numerical-wide": 1, "exact": 1 };

  function hashStr(s) {
    var h = 0;
    for (var i = 0; i < s.length; i++) h = (h * 31 + s.charCodeAt(i)) | 0;
    return h;
  }

  function feedLineFor(rec) {
    var bank = FEED_PHRASES[rec.game] || FEED_PHRASES.standoff;
    var list = KILLED_TIERS[rec.tier] ? bank.killed : bank.survivor;
    var idx = Math.abs(hashStr(String(rec.id || rec.game))) % list.length;
    return list[idx];
  }

  var feedTrack = document.getElementById("feed-track");

  function renderFeed(records) {
    if (!records || records.length === 0) {
      feedTrack.classList.add("paused");
      feedTrack.innerHTML = '<span class="feed-msg">the floor is quiet — nobody’s rung the bell yet.</span>';
      return;
    }
    var lines = records.map(feedLineFor);
    var entries = lines.map(function (line) {
      return '<span class="feed-entry">' + line + "</span>";
    });
    // duplicate the run once so the scrolling loop (-50%) is seamless
    var html = entries.join("") + entries.join("");
    feedTrack.classList.remove("paused");
    feedTrack.innerHTML = html;
  }

  function renderFeedOffline() {
    feedTrack.classList.add("paused");
    feedTrack.innerHTML = '<span class="feed-msg">no word from the floor tonight.</span>';
  }

  // ---------- poll loop ----------

  function refresh() {
    if (MOCK) advanceMock();

    getStats()
      .then(renderLedgerStats)
      .catch(function () { renderLedgerStatsOffline(); });

    getCandidates(10)
      .then(function (data) {
        renderFeed(data.candidates);
        renderLedgerRecords(data.candidates);
      })
      .catch(function () {
        renderFeedOffline();
        renderLedgerRecordsOffline();
      });
  }

  var mockBadge = document.getElementById("mock-badge");
  if (MOCK && mockBadge) mockBadge.hidden = false;

  refresh();
  setInterval(refresh, POLL_MS);
})();
