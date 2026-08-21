// api.js — thin HTTP client for the portal API, with a mock-mode switch.
// Real calls go to the same-origin server started by Games/serve.py; mock
// mode (?mock=1) routes every call to Atlas.Mock instead so the whole
// instrument is demoable offline. This module never fabricates a recorded
// score for real mode: every non-mock result is exactly what the server
// returned.
(function () {
  'use strict';

  const params = new URLSearchParams(location.search);
  const MOCK = params.get('mock') === '1';
  const EPS_KILL = 0.02; // mirrors DESIGN.md; rendering-only, server is authoritative at record time.

  function b64urlEncode(obj) {
    const json = JSON.stringify(obj);
    const b64 = btoa(unescape(encodeURIComponent(json)));
    return b64.replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  }

  function b64urlDecode(s) {
    let b64 = s.replace(/-/g, '+').replace(/_/g, '/');
    while (b64.length % 4) b64 += '=';
    const json = decodeURIComponent(escape(atob(b64)));
    return JSON.parse(json);
  }

  function fnv1a(str) {
    let h = 0x811c9dc5;
    for (let i = 0; i < str.length; i++) {
      h ^= str.charCodeAt(i);
      h = Math.imul(h, 0x01000193);
    }
    return (h >>> 0).toString(36);
  }

  function sessionId() {
    let id = localStorage.getItem('atlas:session');
    if (!id) {
      id = window.crypto && crypto.randomUUID
        ? crypto.randomUUID()
        : 'sess-' + Date.now() + '-' + Math.random().toString(36).slice(2);
      localStorage.setItem('atlas:session', id);
    }
    return id;
  }

  async function realFetch(path, opts) {
    let resp;
    try {
      resp = await fetch(path, opts);
    } catch (e) {
      const err = new Error('network error: ' + e.message);
      err.isNetwork = true;
      throw err;
    }
    if (resp.status === 503) {
      const err = new Error('server busy (503)');
      err.isBusy = true;
      throw err;
    }
    if (!resp.ok) {
      let body = null;
      try { body = await resp.json(); } catch (_) { /* ignore */ }
      const err = new Error((body && body.error) || ('HTTP ' + resp.status));
      err.status = resp.status;
      throw err;
    }
    return resp.json();
  }

  function postJson(path, obj) {
    return realFetch(path, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(obj),
    });
  }

  const Api = {
    MOCK,
    EPS_KILL,
    b64urlEncode,
    b64urlDecode,
    fnv1a,
    sessionId,

    getCuratedTables() {
      return MOCK ? window.Atlas.Mock.getCuratedTables() : realFetch('/api/tables/curated');
    },
    getCandidates(limit) {
      return MOCK
        ? window.Atlas.Mock.getCandidates(limit)
        : realFetch('/api/candidates?limit=' + (limit || 50));
    },
    attackBatch(tables, level) {
      return MOCK
        ? window.Atlas.Mock.attackBatch(tables, level)
        : postJson('/api/attack_batch', { tables, level });
    },
    attack(table, level) {
      return MOCK ? window.Atlas.Mock.attack(table, level) : postJson('/api/attack', { table, level });
    },
    getJob(id) {
      return MOCK ? window.Atlas.Mock.getJob(id) : realFetch('/api/jobs/' + encodeURIComponent(id));
    },
    filters(table) {
      return MOCK ? window.Atlas.Mock.filters(table) : postJson('/api/filters', { table });
    },
    postCandidate(payload) {
      return MOCK ? window.Atlas.Mock.postCandidate(payload) : postJson('/api/candidates', payload);
    },
  };

  window.Atlas = window.Atlas || {};
  window.Atlas.Api = Api;
})();
