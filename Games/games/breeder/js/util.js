// Generic helpers shared across the breeder modules. No DOM, no network.

export function clamp(x, lo = -4, hi = 4) {
  return Math.max(lo, Math.min(hi, x));
}

export function clamp01(x) {
  return Math.max(0, Math.min(1, x));
}

export function uuid() {
  if (window.crypto && crypto.randomUUID) return crypto.randomUUID();
  return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, (c) => {
    const r = (Math.random() * 16) | 0;
    const v = c === 'x' ? r : (r & 0x3) | 0x8;
    return v.toString(16);
  });
}

export function cloneTable(table) {
  return table.map((row) => row.slice());
}

export function blankTable() {
  return Array.from({ length: 16 }, () => [0, 0, 0, 0]);
}

// Deterministic 32-bit hash of a table's contents, quantized so float noise
// from serialization/round-tripping doesn't change the hash. Same table
// (same numbers) must always produce the same creature, so this hash also
// seeds the small decorative PRNG used for limb/spot placement.
export function hashTable(table) {
  let h = 0x811c9dc5;
  for (const row of table) {
    for (const v of row) {
      const q = Math.round(v * 1000) | 0;
      h ^= q;
      h = Math.imul(h, 0x01000193);
    }
  }
  return h >>> 0;
}

// mulberry32: tiny deterministic PRNG, seeded from hashTable() so the same
// table always yields the same decorative jitter.
export function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

export function b64urlDecodeToString(str) {
  let s = str.replace(/-/g, '+').replace(/_/g, '/');
  while (s.length % 4) s += '=';
  return atob(s);
}

// Accepts the ?table= query param: urlsafe-base64 JSON of the 16x4 wire
// format. Returns null on any malformed input rather than throwing.
export function decodeTableParam(param) {
  try {
    const json = b64urlDecodeToString(param);
    const table = JSON.parse(json);
    if (!Array.isArray(table) || table.length !== 16) return null;
    for (const row of table) {
      if (!Array.isArray(row) || row.length !== 4) return null;
    }
    return table;
  } catch (e) {
    return null;
  }
}
