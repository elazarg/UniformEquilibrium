// Ancestry persistence and the compact lineage strip. Tracks the chain of
// champion tables (the best-scoring specimen seen at each generation where
// the champion improved), so a player can see the path from seed to current
// best and so provenance can be attached to auto-submitted candidates.

const STORE_KEY = 'breeder.state.v1';

export function loadState() {
  try {
    const raw = localStorage.getItem(STORE_KEY);
    if (!raw) return null;
    return JSON.parse(raw);
  } catch (e) {
    return null;
  }
}

export function saveState(state) {
  try {
    localStorage.setItem(STORE_KEY, JSON.stringify(state));
  } catch (e) {
    // storage full or unavailable (private browsing); play on without it
  }
}

export function clearState() {
  try {
    localStorage.removeItem(STORE_KEY);
  } catch (e) {
    /* ignore */
  }
}

// Renders the champion path as a bare filmstrip: creatures only, no digits,
// no headings — the more recent ancestor is simply drawn larger/brighter
// (see .lineage-node.current in style.css). Raw generation numbers and
// scores live in the hood panel, never here.
export function renderLineageStrip(container, championPath, renderThumb) {
  if (!championPath.length) {
    container.innerHTML = '';
    return;
  }
  const nodes = championPath
    .map((node, idx) => {
      const isLast = idx === championPath.length - 1;
      return `<div class="lineage-node${isLast ? ' current' : ''}">${renderThumb(node.table, node.score)}</div>`;
    })
    .join('<span class="lineage-arrow">&rsaquo;</span>');
  container.innerHTML = nodes;
}
