/* standoff — the portal API client.
 *
 * Two backends behind one interface:
 *   live  — fetch() against the portal server (DESIGN.md "HTTP API").
 *   mock  — ?mock=1: contract-shaped responses computed by js/eval.js, so the
 *           whole game is playable offline. Mock results are marked
 *           `mock: true` and the UI says so on screen.
 *
 * A 503 from the live server means the engine is still warming up. That is
 * surfaced as a retryable SaloonClosed condition, not an error dialog.
 */
(function (root) {
  'use strict';

  var E = root.SOEval;

  function SaloonClosed(message) { this.message = message || 'engine warming up'; }
  SaloonClosed.prototype.toString = function () { return this.message; };

  function ApiError(message, status) { this.message = message; this.status = status; }
  ApiError.prototype.toString = function () { return this.message; };

  // ------------------------------------------------------------ live mode --

  function request(method, path, body) {
    var options = { method: method, headers: { 'Accept': 'application/json' } };
    if (body !== undefined) {
      options.headers['Content-Type'] = 'application/json';
      options.body = JSON.stringify(body);
    }
    return root.fetch(path, options).then(function (response) {
      if (response.status === 503) {
        return response.text().then(function () { throw new SaloonClosed(); });
      }
      return response.text().then(function (text) {
        var payload = null;
        try { payload = text ? JSON.parse(text) : null; } catch (e) { payload = null; }
        if (!response.ok) {
          var msg = (payload && payload.error) || ('HTTP ' + response.status);
          throw new ApiError(msg, response.status);
        }
        if (payload === null) throw new ApiError('malformed response', response.status);
        return payload;
      });
    }, function (networkError) {
      throw new ApiError('no answer from the house (' + networkError.message + ')', 0);
    });
  }

  // ------------------------------------------------------------ mock mode --

  var MOCK_LIBRARY = [
    {
      id: 'lib-sv-pair',
      note: 'the Solan-Vieille repair: pairs {Cassidy,Delacroix} and {Boone,Rye}',
      profile: {
        period: 2,
        hazards: [[0.2540, 0.0, 0.2540, 0.0], [0.0, 0.2660, 0.0, 0.2660]]
      }
    },
    {
      id: 'lib-slow-drift',
      note: 'a slow stationary drift found on Ashfield Pot',
      profile: { period: 1, hazards: [[0.0724, 0.3010, 0.0106, 0.4400]] }
    },
    {
      id: 'lib-carousel',
      note: 'the Kettleman rotation, four beats',
      profile: {
        period: 4,
        hazards: [[0.31, 0, 0, 0], [0, 0.29, 0, 0], [0, 0, 0.33, 0], [0, 0, 0, 0.27]]
      }
    },
    {
      id: 'lib-twin-fast',
      note: 'a fast paired draw off Marlowe’s Ledger',
      profile: { period: 2, hazards: [[0.51, 0.0, 0.0, 0.49], [0.0, 0.47, 0.53, 0.0]] }
    }
  ];

  var mockState = {
    library: MOCK_LIBRARY.slice(),
    candidates: [],
    jobs: {},
    jobSeq: 0
  };

  function delay(ms, value) {
    return new Promise(function (resolve) { setTimeout(function () { resolve(value); }, ms); });
  }

  function mockAttack(table, level) {
    var started = (root.performance || Date).now();
    var breakdown = {};
    var replay = E.libraryReplay(table, mockState.library);
    if (replay.profile) {
      breakdown.library_replay = {
        exploitability: replay.exploitability,
        profile: replay.profile,
        source: replay.entry ? replay.entry.note : null
      };
    }
    if (level !== 'replay') {
      var wide = (level === 'deep');
      breakdown.stationary = E.attackStationary(table, wide ? 'wide' : 'quick');
      if (level === 'standard' || level === 'deep') {
        breakdown.one_quitter_cyclic = E.attackOneQuitter(table, wide ? 'wide' : 'quick');
        breakdown.general_periodic = E.attackGeneralPeriodic(table, wide ? 'wide' : 'quick');
        breakdown.two_quitter_periodic = E.attackTwoQuitter(table, wide ? 'wide' : 'quick');
      }
    }
    var score = Infinity, binding = null;
    for (var key in breakdown) {
      if (breakdown[key].exploitability < score) {
        score = breakdown[key].exploitability;
        binding = key;
      }
    }
    if (!isFinite(score)) { score = Infinity; binding = null; }
    var elapsed = ((root.performance || Date).now() - started) / 1000;
    return {
      score: score, binding_attack: binding, level: level,
      elapsed: elapsed, breakdown: breakdown, mock: true
    };
  }

  function tierFor(response, killed) {
    if (killed) {
      if (response.score < 0.5 * E.EPS_KILL) return 'numerical-wide';
      return 'numerical-narrow';
    }
    if (response.level === 'deep') return 'survivor-deep';
    if (response.level === 'standard') return 'survivor-standard';
    if (response.level === 'quick') return 'survivor-quick';
    return 'unattacked';
  }

  function mockDispatch(method, path, body) {
    if (path === '/api/tables/curated') {
      return delay(120, { tables: root.SOCuratedMock, mock: true });
    }
    if (path.indexOf('/api/stats') === 0) {
      return delay(80, {
        candidates: mockState.candidates.length,
        best_score: mockState.candidates.reduce(function (a, c) {
          return Math.max(a, (c.evaluation && c.evaluation.score) || 0);
        }, 0),
        library_profiles: mockState.library.length,
        kills: mockState.library.length,
        games: ['standoff', 'sequencer', 'breeder', 'atlas'],
        mock: true
      });
    }
    if (path === '/api/filters') {
      var result = E.runFilters(body.table, E.MARGIN);
      return delay(40, { pass: result.pass, filters: result.filters, mock: true });
    }
    if (path === '/api/evaluate') {
      var detail = E.evaluateDetailed(body.table, body.profile.hazards);
      return delay(30, {
        exploitability: detail.exploitability,
        per_player: detail.per_player,
        on_path: detail.on_path,
        best_deviations: detail.best_deviations,
        mock: true
      });
    }
    if (path === '/api/attack') {
      if (body.level === 'deep') {
        var id = 'mock-job-' + (++mockState.jobSeq);
        mockState.jobs[id] = { status: 'running', result: null };
        var table = body.table;
        setTimeout(function () {
          try {
            mockState.jobs[id] = { status: 'done', result: mockAttack(table, 'deep') };
          } catch (err) {
            mockState.jobs[id] = { status: 'error', result: String(err) };
          }
        }, 7000 + Math.random() * 4000);
        return delay(200, { job: id, mock: true });
      }
      var cost = body.level === 'replay' ? 90 : (body.level === 'quick' ? 260 : 520);
      var response = mockAttack(body.table, body.level);
      return delay(cost, response);
    }
    if (path.indexOf('/api/jobs/') === 0) {
      var jobId = path.slice('/api/jobs/'.length);
      var job = mockState.jobs[jobId];
      if (!job) return Promise.reject(new ApiError('no such job', 404));
      return delay(60, { status: job.status, result: job.result, mock: true });
    }
    if (path === '/api/candidates' && method === 'POST') {
      var evaluation = mockAttack(body.table, 'standard');
      var killed = evaluation.score <= E.EPS_KILL;
      var record = {
        id: 'mock-cand-' + (mockState.candidates.length + 1),
        created: new Date().toISOString(),
        table: body.table,
        game: body.game,
        session: body.session,
        provenance: body.provenance,
        evaluation: evaluation,
        tier: tierFor(evaluation, killed),
        status: killed ? 'killed' : 'proposed',
        killed_by: killed ? evaluation.breakdown[evaluation.binding_attack].profile : null
      };
      mockState.candidates.unshift(record);
      return delay(600, { id: record.id, record: record, mock: true });
    }
    if (path.indexOf('/api/candidates') === 0) {
      return delay(80, { candidates: mockState.candidates, mock: true });
    }
    if (path === '/api/profiles' && method === 'POST') {
      var pid = 'mock-prof-' + (mockState.library.length + 1);
      mockState.library.push({
        id: pid, note: 'learned from a standoff run', profile: body.profile
      });
      return delay(120, { id: pid, mock: true });
    }
    return Promise.reject(new ApiError('mock has no route for ' + path, 404));
  }

  // ---------------------------------------------------------------- facade --

  var params = new URLSearchParams(root.location ? root.location.search : '');
  var MOCK = params.get('mock') === '1';

  function call(method, path, body) {
    if (MOCK) {
      return new Promise(function (resolve, reject) {
        // Keep the frame free: heavy local batteries run off the paint path.
        setTimeout(function () {
          mockDispatch(method, path, body).then(resolve, reject);
        }, 0);
      });
    }
    return request(method, path, body);
  }

  var API = {
    mock: MOCK,
    SaloonClosed: SaloonClosed,
    ApiError: ApiError,

    curated: function () { return call('GET', '/api/tables/curated'); },
    stats: function () { return call('GET', '/api/stats'); },
    filters: function (table) { return call('POST', '/api/filters', { table: table }); },
    evaluate: function (table, profile) {
      return call('POST', '/api/evaluate', { table: table, profile: profile });
    },
    attack: function (table, level) {
      return call('POST', '/api/attack', { table: table, level: level });
    },
    job: function (id) { return call('GET', '/api/jobs/' + encodeURIComponent(id)); },
    submitCandidate: function (payload) {
      return call('POST', '/api/candidates', payload);
    },
    submitProfile: function (profile, source) {
      return call('POST', '/api/profiles', { profile: profile, source: source });
    },

    /* Poll a deep-attack job to completion. `onTick` is called on every poll
     * with the elapsed seconds so the waiting theater can breathe. */
    awaitJob: function (id, onTick) {
      var started = Date.now();
      return new Promise(function (resolve, reject) {
        var poll = function () {
          API.job(id).then(function (state) {
            var elapsed = (Date.now() - started) / 1000;
            if (onTick) onTick(elapsed, state.status);
            if (state.status === 'done') return resolve(state.result);
            if (state.status === 'error') {
              return reject(new ApiError(String(state.result || 'job failed'), 500));
            }
            setTimeout(poll, 700);
          }, function (err) {
            if (err instanceof SaloonClosed) { setTimeout(poll, 1500); return; }
            reject(err);
          });
        };
        setTimeout(poll, 700);
      });
    },

    /* Retry wrapper for the saloon-warming-up case. `onWait` reports each
     * retry so the loading screen can stay in fiction. */
    patient: function (thunk, onWait, attempts) {
      attempts = attempts === undefined ? 20 : attempts;
      return thunk().catch(function (err) {
        if (err instanceof SaloonClosed && attempts > 0) {
          if (onWait) onWait(attempts);
          return new Promise(function (resolve) { setTimeout(resolve, 1400); })
            .then(function () { return API.patient(thunk, onWait, attempts - 1); });
        }
        throw err;
      });
    }
  };

  root.SOApi = API;
})(window);
