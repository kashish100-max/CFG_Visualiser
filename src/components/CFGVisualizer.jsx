import { useState, useEffect, useRef, useCallback } from "react";

// ─── CFG PARSER ────────────────────────────────────────────────────────────────
function parseGrammar(text) {
  const rules = {};
  const lines = text.trim().split("\n");
  for (const line of lines) {
    const parts = line.split("->");
    if (parts.length < 2) continue;
    const lhs = parts[0].trim();
    const rhs = parts.slice(1).join("->").trim();
    if (!lhs || !rhs) continue;
    const alts = rhs.split("|").map((s) => s.trim()).filter(Boolean);
    if (alts.length > 0) {
      if (rules[lhs]) rules[lhs] = [...rules[lhs], ...alts];
      else rules[lhs] = alts;
    }
  }
  return rules;
}

function tokenizeRHS(str) {
  if (!str || str === "ε") return [];
  return str.split("").filter(s => s.trim() !== "");
}

// ─── DERIVATION ENGINE ─────────────────────────────────────────────────────────
function deriveSteps(rules, startSymbol, target, mode = "lmd") {
  const nts = new Set(Object.keys(rules));
  const targetStr = target.join("");
  const queue = [{ sentential: [startSymbol], path: [[startSymbol]] }];
  const visited = new Set([startSymbol]);
  const MAX_ITERATIONS = 8000;
  let iterations = 0;
  while (queue.length > 0 && iterations < MAX_ITERATIONS) {
    iterations++;
    const { sentential: current, path } = queue.shift();
    const currentStr = current.join("");
    if (currentStr === targetStr && current.every(t => !nts.has(t))) return path;
    if (current.length > targetStr.length + 6 || path.length > 30) continue;
    let termPrefix = "";
    for (const sym of current) { if (!nts.has(sym)) termPrefix += sym; else break; }
    if (termPrefix && !targetStr.startsWith(termPrefix)) continue;
    let termSuffix = "";
    for (let i = current.length - 1; i >= 0; i--) { if (!nts.has(current[i])) termSuffix = current[i] + termSuffix; else break; }
    if (termSuffix && !targetStr.endsWith(termSuffix)) continue;
    const ntIdxs = current.reduce((a, t, i) => { if (nts.has(t)) a.push(i); return a; }, []);
    if (ntIdxs.length === 0) continue;
    const idx = mode === "lmd" ? ntIdxs[0] : ntIdxs[ntIdxs.length - 1];
    const sym = current[idx];
    const sortedAlts = [...(rules[sym] || [])].sort((a, b) => {
      const aR = a.includes(sym), bR = b.includes(sym);
      if (aR && !bR) return 1; if (!aR && bR) return -1; return a.length - b.length;
    });
    for (const alt of sortedAlts) {
      const altToks = (alt === "ε" || alt === "") ? [] : alt.trim().split("");
      const next = [...current.slice(0, idx), ...altToks, ...current.slice(idx + 1)];
      const k = next.join("") + "|" + next.length;
      if (!visited.has(k)) { visited.add(k); queue.push({ sentential: next, path: [...path, next] }); }
    }
  }
  return [];
}

function tokenizeProduction(alt) {
  if (!alt || alt === "ε") return [];
  const trimmed = alt.trim();
  if (trimmed.includes(" ")) return trimmed.split(/\s+/).filter(Boolean);
  return trimmed.split("").filter(s => s.trim() !== "");
}

// ─── EARLEY PARSER — extracts ALL distinct parse trees ───────────────────────
function earleyParseAll(rules, startSymbol, inputStr, MAX_TREES = 8) {
  const nts = new Set(Object.keys(rules));
  const n = inputStr.length;
  const chart = Array.from({ length: n + 1 }, () => []);

  function addItem(i, item) {
    const key = `${item.lhs}|${item.rhs.join(",")}|${item.dot}|${item.origin}`;
    if (!chart[i]._keys) chart[i]._keys = new Set();
    if (chart[i]._keys.has(key)) return false;
    chart[i]._keys.add(key);
    chart[i].push(item);
    return true;
  }

  for (const alt of (rules[startSymbol] || []))
    addItem(0, { lhs: startSymbol, rhs: tokenizeProduction(alt), dot: 0, origin: 0, backpointers: [] });

  for (let i = 0; i <= n; i++) {
    let j = 0;
    while (j < chart[i].length) {
      const item = chart[i][j++];
      const nextSym = item.rhs[item.dot];
      if (nextSym === undefined) {
        for (const waiting of chart[item.origin]) {
          if (waiting.rhs[waiting.dot] === item.lhs) {
            const ni = { lhs: waiting.lhs, rhs: waiting.rhs, dot: waiting.dot + 1, origin: waiting.origin, backpointers: [] };
            if (addItem(i, ni)) { ni.backpointers.push({ prev: waiting, completed: item, pos: i }); }
            else {
              const ex = chart[i].find(x => x.lhs === ni.lhs && x.rhs.join(",") === ni.rhs.join(",") && x.dot === ni.dot && x.origin === ni.origin);
              if (ex) ex.backpointers.push({ prev: waiting, completed: item, pos: i });
            }
          }
        }
      } else if (nts.has(nextSym)) {
        for (const alt of (rules[nextSym] || []))
          addItem(i, { lhs: nextSym, rhs: tokenizeProduction(alt), dot: 0, origin: i, backpointers: [] });
      } else {
        if (i < n && inputStr[i] === nextSym) {
          const ni = { lhs: item.lhs, rhs: item.rhs, dot: item.dot + 1, origin: item.origin, backpointers: [] };
          if (addItem(i + 1, ni)) ni.backpointers.push({ prev: item, scanned: nextSym, pos: i + 1 });
        }
      }
    }
  }

  const completedItems = chart[n].filter(x => x.lhs === startSymbol && x.dot === x.rhs.length && x.origin === 0);
  if (completedItems.length === 0) return [];

  const results = [];
  const seenSigs = new Set();

  function treeToSig(node) {
    if (!node.children || node.children.length === 0) return node.value;
    return node.value + "(" + node.children.map(treeToSig).join(",") + ")";
  }

  function extractTreeOrd(item, endPos, memo, ord, depth = 0) {
    if (depth > 80) return null;
    const key = `${item.lhs}|${item.rhs.join(",")}|${item.dot}|${item.origin}|${endPos}`;
    if (memo.has(key)) return memo.get(key);
    memo.set(key, null); // cycle guard
    if (item.dot === 0 && item.rhs.length > 0) { const r = { value: item.lhs, children: [], rule: null }; memo.set(key, r); return r; }
    if (item.dot === 0 && item.rhs.length === 0) {
      // This is S → ε  (epsilon production, seeded directly, no backpointers)
      const r = { value: item.lhs, children: [{ value: "ε", children: [], isTerminal: true, rule: null }], rule: item.lhs + " → ε" };
      memo.set(key, r); return r;
    }
    const bps = [...item.backpointers];
    if (ord > 0) bps.sort((a, b) => {
      const ka = JSON.stringify(a.completed ? a.completed.rhs : a.scanned || "");
      const kb = JSON.stringify(b.completed ? b.completed.rhs : b.scanned || "");
      return (ord % 2 === 0) ? (ka < kb ? -1 : 1) : (ka > kb ? -1 : 1);
    });
    for (const bp of bps) {
      if (bp.scanned !== undefined) {
        const prev = extractTreeOrd(bp.prev, bp.pos - 1, memo, ord, depth + 1);
        if (!prev) continue;
        const result = { value: prev.value, children: [...prev.children, { value: bp.scanned, children: [], isTerminal: true, rule: null }], rule: prev.rule };
        memo.set(key, result); return result;
      } else if (bp.completed !== undefined) {
        if (bp.isEpsilon) {
          const prev = extractTreeOrd(bp.prev, endPos, memo, ord, depth + 1);
          if (!prev) continue;
          const result = { value: prev.value, children: [...prev.children, { value: bp.completed.lhs, children: [{ value: "ε", children: [], isTerminal: true, rule: null }], rule: bp.completed.lhs + " → ε" }], rule: prev.rule };
          memo.set(key, result); return result;
        }
        const cSub = extractSubTreeOrd(bp.completed, bp.completed.origin, bp.pos, memo, ord, depth + 1);
        if (!cSub) continue;
        const prev = extractTreeOrd(bp.prev, bp.completed.origin, memo, ord, depth + 1);
        if (!prev) continue;
        const result = { value: prev.value, children: [...prev.children, cSub], rule: prev.rule };
        memo.set(key, result); return result;
      }
    }
    return null;
  }

  function extractSubTreeOrd(item, startPos, endPos, memo, ord, depth = 0) {
    if (depth > 80) return null;
    const key2 = `sub|${item.lhs}|${item.rhs.join(",")}|${startPos}|${endPos}`;
    if (memo.has(key2)) return memo.get(key2);
    memo.set(key2, null); // cycle guard
    const matches = [...chart[endPos].filter(x => x.lhs === item.lhs && x.rhs.join(",") === item.rhs.join(",") && x.dot === x.rhs.length && x.origin === startPos)];
    matches.sort((a, b) => (ord % 2 === 0) ? a.rhs.length - b.rhs.length : b.rhs.length - a.rhs.length);
    for (const mi of matches) {
      const t = extractTreeOrd(mi, endPos, memo, ord, depth + 1);
      if (t) {
        const ruleStr = item.lhs + " → " + (item.rhs.length === 0 ? "ε" : item.rhs.join(""));
        const result = { value: item.lhs, children: t.children, rule: ruleStr };
        memo.set(key2, result); return result;
      }
    }
    if (item.rhs.length === 0) {
      const result = { value: item.lhs, children: [{ value: "ε", children: [], isTerminal: true, rule: null }], rule: item.lhs + " → ε" };
      memo.set(key2, result); return result;
    }
    return null;
  }

  for (let ord = 0; ord < 12 && results.length < MAX_TREES; ord++) {
    for (const ci of completedItems) {
      if (results.length >= MAX_TREES) break;
      const memo = new Map();
      const tree = extractTreeOrd(ci, n, memo, ord);
      if (tree) {
        const sig = treeToSig(tree);
        if (!seenSigs.has(sig)) {
          seenSigs.add(sig);
          const rootRule = ci.lhs + " → " + (ci.rhs.length === 0 ? "ε" : ci.rhs.join(""));
          results.push({ value: ci.lhs, children: tree.children, rule: rootRule });
        }
      }
    }
  }
  return results;
}

// ─── SMART ERROR ANALYSIS ────────────────────────────────────────────────────
function analyzeDerivationFailure(rules, startSymbol, targetStr) {
  const nts = new Set(Object.keys(rules));
  const info = { reason: "not_derivable", details: "", stuckNT: null, mismatchPos: -1, unreachable: [] };

  // 1. Unreachable check
  const reachable = new Set([startSymbol]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const [nt, alts] of Object.entries(rules)) {
      if (!reachable.has(nt)) continue;
      for (const alt of alts)
        for (const ch of tokenizeProduction(alt))
          if (nts.has(ch) && !reachable.has(ch)) { reachable.add(ch); changed = true; }
    }
  }
  const unreachable = [...nts].filter(n => !reachable.has(n));
  if (unreachable.length > 0) {
    info.unreachable = unreachable; info.reason = "unreachable";
    info.details = `Non-terminal(s) ${unreachable.join(", ")} are defined but unreachable from start symbol "${startSymbol}". They are dead code and can never contribute to any derivation.`;
    return info;
  }

  // 2. Unproductive check
  const productive = new Set();
  changed = true;
  while (changed) {
    changed = false;
    for (const [nt, alts] of Object.entries(rules)) {
      if (productive.has(nt)) continue;
      for (const alt of alts) {
        const toks = tokenizeProduction(alt);
        if (toks.length === 0 || toks.every(t => !nts.has(t) || productive.has(t))) { productive.add(nt); changed = true; break; }
      }
    }
  }
  const stuck = [...nts].filter(n => !productive.has(n));
  if (stuck.length > 0) {
    info.stuckNT = stuck[0]; info.reason = "stuck_nt";
    info.details = `Non-terminal "${stuck[0]}" can never produce a purely terminal string — every derivation path through it leads to infinite recursion or another unproductive symbol.`;
    return info;
  }

  // 3. Prefix mismatch
  const target = targetStr;
  let bestMatchLen = 0;
  const q = [{ sent: [startSymbol], depth: 0 }];
  const seen = new Set([startSymbol + "|0"]);
  for (let iter = 0; iter < 4000 && q.length > 0; iter++) {
    const { sent, depth } = q.shift();
    const allTerms = sent.every(t => !nts.has(t));
    if (allTerms) {
      const s = sent.join("");
      let ml = 0;
      for (let i = 0; i < Math.min(s.length, target.length); i++) { if (s[i] === target[i]) ml = i + 1; else break; }
      if (ml > bestMatchLen) bestMatchLen = ml;
      continue;
    }
    if (sent.length > target.length + 2 || depth > 18) continue;
    const ntIdx = sent.findIndex(t => nts.has(t));
    if (ntIdx === -1) continue;
    let termPfx = "";
    for (let k = 0; k < sent.length; k++) { if (!nts.has(sent[k])) termPfx += sent[k]; else break; }
    if (termPfx && !target.startsWith(termPfx)) continue;
    for (const alt of (rules[sent[ntIdx]] || [])) {
      const toks = tokenizeProduction(alt);
      const next = [...sent.slice(0, ntIdx), ...toks, ...sent.slice(ntIdx + 1)];
      const k = next.join("") + "|" + depth;
      if (!seen.has(k)) { seen.add(k); q.push({ sent: next, depth: depth + 1 }); }
    }
  }
  if (bestMatchLen > 0) {
    info.mismatchPos = bestMatchLen; info.reason = "mismatch";
    info.details = `The grammar can match the first ${bestMatchLen} character${bestMatchLen > 1 ? "s" : ""} "${target.slice(0, bestMatchLen)}" but fails at position ${bestMatchLen + 1} — no production can generate "${target[bestMatchLen] || "∅"}" in that context.`;
  } else {
    info.reason = "no_match";
    info.details = `No derivation from "${startSymbol}" can produce any prefix of "${target}". Check that terminal symbols in your grammar match the characters in the target string.`;
  }
  return info;
}

// ─── AUTO-GENERATE VALID STRING ──────────────────────────────────────────────
function generateValidString(rules, startSymbol, targetLen) {
  if (!rules || !startSymbol) return null;
  const nts = new Set(Object.keys(rules));
  const q = [{ sent: [startSymbol], depth: 0 }];
  const seen = new Set([startSymbol]);
  let best = null;
  for (let iter = 0; iter < 6000 && q.length > 0; iter++) {
    const { sent, depth } = q.shift();
    if (sent.every(t => !nts.has(t))) {
      const s = sent.join("");
      if (targetLen === 0 || sent.length === targetLen) return s;
      if (!best || Math.abs(sent.length - targetLen) < Math.abs(best.length - targetLen)) best = s;
      continue;
    }
    if (sent.length > Math.max(targetLen, 2) + 4 || depth > 30) continue;
    const ntIdx = sent.findIndex(t => nts.has(t));
    if (ntIdx === -1) continue;
    const alts = [...(rules[sent[ntIdx]] || [])].sort((a, b) => a.length - b.length);
    for (const alt of alts) {
      const toks = tokenizeProduction(alt);
      const next = [...sent.slice(0, ntIdx), ...toks, ...sent.slice(ntIdx + 1)];
      const key = next.join("") + "|" + depth;
      if (!seen.has(key)) { seen.add(key); q.push({ sent: next, depth: depth + 1 }); }
    }
  }
  return best;
}

// ─── PUBLIC PARSE API ────────────────────────────────────────────────────────
function buildParseTree(rules, startSymbol, targetStr) {
  try {
    const trees = earleyParseAll(rules, startSymbol, targetStr, 8);
    if (!trees || trees.length === 0) return null;
    return { node: trees[0], allTrees: trees, isAmbiguous: trees.length > 1 };
  } catch (e) { return null; }
}

// ─── LAYOUT ──────────────────────────────────────────────────────────────────
function calculateLayout(node, depth = 0, xOffset = 0) {
  node.depth = depth;
  if (!node.children || node.children.length === 0) { node.x = xOffset; return 1; }
  let totalWidth = 0, currentX = xOffset;
  node.children.forEach(child => { const w = calculateLayout(child, depth + 1, currentX); totalWidth += w; currentX += w; });
  node.x = (node.children[0].x + node.children[node.children.length - 1].x) / 2;
  return totalWidth;
}
function flattenTree(node, arr = []) { arr.push(node); (node.children || []).forEach(c => flattenTree(c, arr)); return arr; }

// ─── PRODUCTION RULE HELPER ───────────────────────────────────────────────────
function getProductionRule(steps, stepIndex, rules, mode) {
  if (stepIndex === 0 || !steps[stepIndex - 1] || !steps[stepIndex]) return null;
  const prev = steps[stepIndex - 1], curr = steps[stepIndex];
  const nts = new Set(Object.keys(rules));
  const ntIdxs = prev.reduce((a, t, i) => { if (nts.has(t)) a.push(i); return a; }, []);
  if (ntIdxs.length === 0) return null;
  const idx = mode === "lmd" ? ntIdxs[0] : ntIdxs[ntIdxs.length - 1];
  const expandedNT = prev[idx];
  const beforeStr = prev.slice(0, idx).join(""), afterStr = prev.slice(idx + 1).join("");
  const currStr = curr.join("");
  let rhs = "";
  if (currStr.startsWith(beforeStr) && currStr.endsWith(afterStr))
    rhs = currStr.slice(beforeStr.length, currStr.length - afterStr.length || undefined);
  if (!rhs) rhs = "ε";
  return `${expandedNT} → ${rhs}`;
}

// Returns { ruleStr, expandedNT, activeIdx, rhs } for notebook rendering
function getProductionMeta(steps, stepIndex, rules, mode) {
  if (stepIndex === 0 || !steps[stepIndex - 1] || !steps[stepIndex]) return null;
  const prev = steps[stepIndex - 1], curr = steps[stepIndex];
  const nts = new Set(Object.keys(rules));
  const ntIdxs = prev.reduce((a, t, i) => { if (nts.has(t)) a.push(i); return a; }, []);
  if (ntIdxs.length === 0) return null;
  const idx = mode === "lmd" ? ntIdxs[0] : ntIdxs[ntIdxs.length - 1];
  const expandedNT = prev[idx];
  const beforeStr = prev.slice(0, idx).join(""), afterStr = prev.slice(idx + 1).join("");
  const currStr = curr.join("");
  let rhs = "";
  if (currStr.startsWith(beforeStr) && currStr.endsWith(afterStr))
    rhs = currStr.slice(beforeStr.length, currStr.length - afterStr.length || undefined);
  if (!rhs) rhs = "ε";
  // activeIdx = position in PREV step's sentential form that was expanded
  return { ruleStr: `${expandedNT} → ${rhs}`, expandedNT, activeIdx: idx, rhs };
}

// ─── ANIMATED COUNTER ─────────────────────────────────────────────────────────
function AnimatedCount({ value, color = "#818cf8" }) {
  const startVal = useRef(value + 50 + Math.floor(Math.random() * 50));
  const [displayed, setDisplayed] = useState(startVal.current);
  const prevRef = useRef(null);
  useEffect(() => {
    const from = prevRef.current === null ? startVal.current : prevRef.current;
    const to = value;
    prevRef.current = to;
    const steps = 35, duration = 1100;
    let step = 0;
    const timer = setInterval(() => {
      step++;
      const eased = 1 - Math.pow(1 - step / steps, 3);
      setDisplayed(Math.round(from + (to - from) * eased));
      if (step >= steps) { clearInterval(timer); setDisplayed(to); }
    }, duration / steps);
    return () => clearInterval(timer);
  }, [value]);
  return <span style={{ color, fontFamily: "'JetBrains Mono'", fontWeight: 700 }}>{displayed}</span>;
}

// ─── SINGLE TREE SVG (step-by-step manual control + hover tooltip) ────────────
function SingleTreeSVG({ tree, rules, animationKey, treeIndex }) {
  const [currentStep, setCurrentStep] = useState(0);
  const [isPlaying, setIsPlaying] = useState(false);
  const [hoveredNode, setHoveredNode] = useState(null);
  const playTimerRef = useRef(null);
  const svgRef = useRef(null);

  const localTree = JSON.parse(JSON.stringify(tree));
  calculateLayout(localTree);
  const allNodes = flattenTree(localTree);
  const nts = new Set(Object.keys(rules));
  const bfsOrder = [];
  const bq = [localTree];
  while (bq.length > 0) { const nd = bq.shift(); bfsOrder.push(nd); (nd.children || []).forEach(c => bq.push(c)); }
  const totalNodes = bfsOrder.length;

  // Reset step when tree changes
  useEffect(() => {
    setCurrentStep(0);
    setIsPlaying(false);
    if (playTimerRef.current) clearInterval(playTimerRef.current);
  }, [animationKey, treeIndex]);

  // Auto-play logic
  useEffect(() => {
    if (isPlaying) {
      playTimerRef.current = setInterval(() => {
        setCurrentStep(prev => {
          if (prev >= totalNodes) { setIsPlaying(false); return prev; }
          return prev + 1;
        });
      }, 380);
    } else {
      if (playTimerRef.current) clearInterval(playTimerRef.current);
    }
    return () => { if (playTimerRef.current) clearInterval(playTimerRef.current); };
  }, [isPlaying, totalNodes]);

  const handleForward  = () => setCurrentStep(s => Math.min(s + 1, totalNodes));
  const handleBackward = () => setCurrentStep(s => Math.max(s - 1, 0));
  const handlePlay     = () => { if (currentStep >= totalNodes) setCurrentStep(0); setIsPlaying(p => !p); };
  const handleReset    = () => { setCurrentStep(0); setIsPlaying(false); };

  const R = 22, hGap = 120, vGap = 140, pad = 75;
  const minX = Math.min(...allNodes.map(n => n.x));
  const maxX = Math.max(...allNodes.map(n => n.x));
  const maxD = Math.max(...allNodes.map(n => n.depth));
  const W = Math.max(280, (maxX - minX) * hGap + pad * 2);
  const H = maxD * vGap + pad * 2;
  const getX = x => pad + (x - minX) * hGap;
  const getY = d => pad + d * vGap;
  const visibleSet = new Set(bfsOrder.slice(0, currentStep));

  const btnBase = {
    border: "none", borderRadius: 7, fontSize: 14, fontWeight: 600,
    cursor: "pointer", fontFamily: "inherit", padding: "6px 14px",
    display: "flex", alignItems: "center", gap: 5, transition: "all 0.2s"
  };
  const btnEnabled  = { ...btnBase, background: "linear-gradient(135deg,#6366f1,#8b5cf6)", color: "white",  boxShadow: "0 0 10px rgba(139,92,246,0.3)" };
  const btnDisabled = { ...btnBase, background: "rgba(99,102,241,0.08)",                   color: "#77808b", cursor: "not-allowed" };

  return (
    <div style={{ position: "relative" }}>
      {/* ── Controls row ── */}
      <div style={{ display: "flex", gap: 8, marginBottom: 10, alignItems: "center", flexWrap: "wrap" }}>
        {/* Backward */}
        <button onClick={handleBackward} disabled={currentStep === 0}
          style={currentStep === 0 ? btnDisabled : btnEnabled}>
          ◀ Back
        </button>
        {/* Play / Pause */}
        <button onClick={handlePlay}
          style={btnEnabled}>
          {isPlaying ? "⏸ Pause" : (currentStep >= totalNodes ? "↺ Replay" : "▶ Play")}
        </button>
        {/* Forward */}
        <button onClick={handleForward} disabled={currentStep >= totalNodes}
          style={currentStep >= totalNodes ? btnDisabled : btnEnabled}>
          Next ▶
        </button>
        {/* Reset */}
        <button onClick={handleReset} disabled={currentStep === 0}
          style={currentStep === 0 ? btnDisabled : { ...btnBase, background: "rgba(239,68,68,0.12)", color: "#f87171", border: "1px solid rgba(239,68,68,0.25)" }}>
          ↺ Reset
        </button>
        {/* Step counter */}
        <span style={{ fontSize: 13, color: "#818cf8", fontFamily: "'JetBrains Mono'", marginLeft: "auto", background: "rgba(99,102,241,0.1)", border: "1px solid rgba(99,102,241,0.2)", borderRadius: 6, padding: "4px 10px" }}>
          Step {currentStep} / {totalNodes}
        </span>
        {currentStep === totalNodes && (
          <span style={{ fontSize: 13, color: "#4ade80", fontFamily: "'JetBrains Mono'" }}>✓ Complete</span>
        )}
      </div>
      <div style={{ fontSize: 12, color: "#adafb1", marginBottom: 8, fontFamily: "'JetBrains Mono'" }}>
        Hover nodes for rules
      </div>
      <div style={{ overflowX: "auto" }}>
        <svg ref={svgRef} width={W} height={H} viewBox={`0 0 ${W} ${H}`} style={{ display: "block", margin: "auto" }}>
          <defs>
            {/* markerUnits="userSpaceOnUse" keeps arrow size fixed regardless of strokeWidth.
                markerWidth/Height in px. refX=10 = tip of arrow, so tip touches circle edge. */}
            <marker
              id={`arrow-${animationKey}`}
              markerWidth="18" markerHeight="18"
              refX="18" refY="9"
              orient="auto"
              markerUnits="userSpaceOnUse">
              <path d="M0,0 L0,18 L18,9 z" fill="#a78bfa" />
            </marker>
          </defs>
          {allNodes.map((node, i) =>
            (node.children || []).map((child, ci) => {
              if (!visibleSet.has(node) || !visibleSet.has(child)) return null;

              // Line starts at bottom of parent circle, ends exactly at child circle boundary
              const x1 = getX(node.x);
              const y1 = getY(node.depth) + R;
              const x2 = getX(child.x);
              const y2 = getY(child.depth) - R;

              // Pull back by arrowhead length (10px) so the tip lands on the circle edge
              const dx = x2 - x1, dy = y2 - y1;
              const len = Math.sqrt(dx * dx + dy * dy) || 1;
              const stopX = x2 - (dx / len) * 2;
              const stopY = y2 - (dy / len) * 2;
              const pathLen = Math.round(len) + 10;

              return (
                <g key={`e${i}-${ci}-${animationKey}`}>
                  {/* Subtle glow behind the line */}
                  <line
                    x1={x1} y1={y1} x2={stopX} y2={stopY}
                    stroke="#818cf8" strokeWidth="5" strokeLinecap="butt" strokeOpacity="0.15"
                    strokeDasharray={pathLen} strokeDashoffset={pathLen}
                    style={{ animation: "edgeDraw 0.5s cubic-bezier(0.4,0,0.2,1) forwards" }}
                  />
                  {/* Main straight line with arrowhead marker */}
                  <line
                    x1={x1} y1={y1} x2={stopX} y2={stopY}
                    stroke="#818cf8" strokeWidth="1.8" strokeLinecap="butt"
                    markerEnd={`url(#arrow-${animationKey})`}
                    strokeDasharray={pathLen} strokeDashoffset={pathLen}
                    style={{ animation: "edgeDraw 0.5s cubic-bezier(0.4,0,0.2,1) forwards" }}
                  />
                </g>
              );
            })
          )}
          {bfsOrder.map((node, i) => {
            if (!visibleSet.has(node)) return null;
            let fill = "#3b82f6", stroke = "#1d4ed8";
            if (node.depth === 0) { fill = "#ef4444"; stroke = "#b91c1c"; }
            else if (!nts.has(node.value)) { fill = "#22c55e"; stroke = "#15803d"; }
            const cx = getX(node.x), cy = getY(node.depth);
            const isH = hoveredNode === node;
            return (
              <g key={`n${i}-${animationKey}`}
                style={{ transformOrigin: `${cx}px ${cy}px`, animation: "nodePop 0.5s cubic-bezier(0.34,1.56,0.64,1) forwards", cursor: node.rule ? "pointer" : "default" }}
                onMouseEnter={() => setHoveredNode(node)}
                onMouseLeave={() => setHoveredNode(null)}>
                <circle cx={cx} cy={cy} r={isH ? R + 4 : R} fill={fill} stroke={isH ? "#c084fc" : stroke} strokeWidth={isH ? "3" : "2.3"}
                  style={{ filter: `drop-shadow(0 0 ${isH ? 14 : 7}px ${fill}88)`, transition: "all 0.15s" }} />
                <text x={cx} y={cy} textAnchor="middle" dominantBaseline="central" fill="white" fontSize="13" fontWeight="bold" fontFamily="'JetBrains Mono',monospace">{node.value}</text>
              </g>
            );
          })}
          {hoveredNode && hoveredNode.rule && (() => {
            const cx = getX(hoveredNode.x), cy = getY(hoveredNode.depth);
            const label = hoveredNode.rule;
            const tipW = Math.min(label.length * 7.8 + 24, 280);
            const tipX = Math.max(4, Math.min(cx - tipW / 2, W - tipW - 4));
            const tipY = Math.max(4, cy - R - 46);
            return (
              <g>
                <rect x={tipX} y={tipY} width={tipW} height={28} rx={6} fill="#2e1065" stroke="#a78bfa" strokeWidth="1.5" opacity="0.97" />
                <text x={tipX + tipW / 2} y={tipY + 18} textAnchor="middle" fill="#e9d5ff" fontSize="11.5" fontFamily="'JetBrains Mono',monospace" fontWeight="600">{label}</text>
              </g>
            );
          })()}
        </svg>
      </div>
    </div>
  );
}

// ─── PARSE TREE WRAPPER ───────────────────────────────────────────────────────
function ParseTreeSVG({ rules, startSymbol, targetStr, animationKey, onAmbiguityInfo }) {
  const [selectedTree, setSelectedTree] = useState(0);
  let parseResult = null;
  try { parseResult = buildParseTree(rules, startSymbol, targetStr); } catch (e) { /* silent */ }
  const allTrees = (parseResult && parseResult.allTrees) ? parseResult.allTrees : [];
  const isAmbiguous = allTrees.length > 1;

  useEffect(() => { if (onAmbiguityInfo) onAmbiguityInfo(isAmbiguous, allTrees.length); }, [isAmbiguous, allTrees.length]);
  useEffect(() => { setSelectedTree(0); }, [animationKey]);

  if (allTrees.length === 0)
    return <div style={{ color: "#f87171", padding: "16px 0" }}>Cannot build parse tree for this input.</div>;

  return (
    <div>
      <style>{`
        @keyframes spin { from{transform:rotate(0deg)} to{transform:rotate(360deg)} }
        @keyframes nodePop { 0%{transform:scale(0);opacity:0} 60%{transform:scale(1.18);opacity:1} 100%{transform:scale(1);opacity:1} }
        @keyframes edgeDraw { 0%{stroke-dashoffset:300;opacity:0} 100%{stroke-dashoffset:0;opacity:1} }
      `}</style>
      {isAmbiguous && (
        <div style={{ marginBottom: 14, background: "rgba(251,146,60,0.08)", border: "1px solid rgba(251,146,60,0.4)", borderRadius: 10, padding: "12px 16px" }}>
          <div style={{ display: "flex", alignItems: "center", gap: 8, marginBottom: 8 }}>
            <span style={{ fontSize: 16 }}>⚡</span>
            <span style={{ fontSize: "clamp(12px,1.4vw,14px)", fontWeight: 700, color: "#fb923c" }}>
              Ambiguous Grammar — {allTrees.length} distinct parse tree{allTrees.length > 1 ? "s" : ""} found
            </span>
          </div>
          <div style={{ fontSize: "clamp(10px,1.2vw,12px)", color: "#94a3b8", marginBottom: 10, lineHeight: 1.5 }}>
            The same string has multiple parse trees, proving this grammar is ambiguous. Switch between trees to compare their structures.
          </div>
          <div style={{ display: "flex", gap: 6, flexWrap: "wrap" }}>
            {allTrees.map((_, i) => (
              <button key={i} onClick={() => setSelectedTree(i)} style={{
                background: selectedTree === i ? "rgba(251,146,60,0.22)" : "rgba(99,102,241,0.08)",
                border: selectedTree === i ? "1.5px solid #fb923c" : "1px solid rgba(99,102,241,0.22)",
                borderRadius: 7, padding: "5px 14px", fontSize: 12, fontWeight: 700,
                color: selectedTree === i ? "#fb923c" : "#94a3b8",
                cursor: "pointer", fontFamily: "'JetBrains Mono',monospace", transition: "all 0.2s"
              }}>Tree {i + 1}</button>
            ))}
          </div>
        </div>
      )}
      <SingleTreeSVG key={`${animationKey}-${selectedTree}`} tree={allTrees[Math.min(selectedTree, allTrees.length - 1)]} rules={rules} animationKey={animationKey} treeIndex={selectedTree} />
    </div>
  );
}

// ─── GRID BACKGROUND ──────────────────────────────────────────────────────────
function GridBackground() {
  const canvasRef = useRef(null);
  const mouseRef = useRef({ x: -999, y: -999 });
  useEffect(() => {
    const canvas = canvasRef.current; if (!canvas) return;
    const ctx = canvas.getContext("2d");
    let animId, t = 0;
    const resize = () => { canvas.width = canvas.offsetWidth; canvas.height = canvas.offsetHeight; };
    resize(); window.addEventListener("resize", resize);
    const onMove = (e) => { mouseRef.current = { x: e.clientX, y: e.clientY }; };
    window.addEventListener("mousemove", onMove);
    const draw = () => {
      const { width: W, height: H } = canvas;
      ctx.clearRect(0, 0, W, H);
      const { x: mx, y: my } = mouseRef.current;
      t += 0.002; const gs = 52;
      ctx.strokeStyle = "rgba(99,102,241,0.07)"; ctx.lineWidth = 0.5;
      for (let x = 0; x < W; x += gs) { ctx.beginPath(); ctx.moveTo(x, 0); ctx.lineTo(x, H); ctx.stroke(); }
      for (let y = 0; y < H; y += gs) { ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(W, y); ctx.stroke(); }
      for (let x = 0; x < W + gs; x += gs) {
        for (let y = 0; y < H + gs; y += gs) {
          const dx = x - mx, dy = y - my, dist = Math.sqrt(dx * dx + dy * dy);
          const pull = Math.max(0, 1 - dist / 200);
          const ox = pull * dx * -0.15 + Math.sin(t + x * 0.025) * 1.5;
          const oy = pull * dy * -0.15 + Math.cos(t + y * 0.025) * 1.5;
          ctx.beginPath(); ctx.arc(x + ox, y + oy, 1.5 + pull * 2, 0, Math.PI * 2);
          ctx.fillStyle = `rgba(139,92,246,${0.12 + pull * 0.45})`; ctx.fill();
        }
      }
      animId = requestAnimationFrame(draw);
    };
    draw();
    return () => { cancelAnimationFrame(animId); window.removeEventListener("resize", resize); window.removeEventListener("mousemove", onMove); };
  }, []);
  return <canvas ref={canvasRef} style={{ position: "fixed", inset: 0, width: "100%", height: "100%", pointerEvents: "none", zIndex: 0 }} />;
}

// ─── REVEAL ───────────────────────────────────────────────────────────────────
function Reveal({ children, delay = 0, style = {} }) {
  const ref = useRef(null);
  const [vis, setVis] = useState(false);
  useEffect(() => {
    const obs = new IntersectionObserver(([e]) => { if (e.isIntersecting) setVis(true); }, { threshold: 0.1 });
    if (ref.current) obs.observe(ref.current);
    return () => obs.disconnect();
  }, []);
  return (
    <div ref={ref} style={{ opacity: vis ? 1 : 0, transform: vis ? "translateY(0)" : "translateY(28px)", transition: `opacity 0.65s ease ${delay}ms, transform 0.65s ease ${delay}ms`, ...style }}>
      {children}
    </div>
  );
}

// ─── TOOL PAGE ────────────────────────────────────────────────────────────────
function ToolPage({ onBack }) {
  const [grammarText, setGrammarText] = useState("S -> aSb | ab");
  const [targetStr, setTargetStr] = useState("aaabbb");
  const [lmdSteps, setLmdSteps] = useState([]);
  const [rmdSteps, setRmdSteps] = useState([]);
  const [treeRules, setTreeRules] = useState(null);
  const [treeStart, setTreeStart] = useState(null);
  const [treeTarget, setTreeTarget] = useState("");
  const [error, setError] = useState("");
  const [isCFG, setIsCFG] = useState(true);
  const [nonCFGRule, setNonCFGRule] = useState("");
  const [invalidLhsRule, setInvalidLhsRule] = useState("");
  const [detectedSets, setDetectedSets] = useState(null); // { variables, terminals }
  const [caseIssues, setCaseIssues] = useState(null);     // { errors: [], warnings: [] }
  const [isAmbiguous, setIsAmbiguous] = useState(false);
  const [parseTreeCount, setParseTreeCount] = useState(0);
  const [failureInfo, setFailureInfo] = useState(null);
  const [autoGenStr, setAutoGenStr] = useState(null);
  const [activeTab, setActiveTab] = useState("lmd");
  const [generated, setGenerated] = useState(false);
  const [animationKey, setAnimationKey] = useState(0);
  const [menuOpen, setMenuOpen] = useState(false);

  const generate = useCallback(() => {
    setError(""); setIsCFG(true); setNonCFGRule(""); setInvalidLhsRule(""); setDetectedSets(null); setCaseIssues(null);
    setIsAmbiguous(false); setParseTreeCount(0); setFailureInfo(null); setAutoGenStr(null);
    setLmdSteps([]); setRmdSteps([]); setTreeRules(null); setTreeStart(null); setTreeTarget("");
    try {
      const rules = parseGrammar(grammarText);
      if (Object.keys(rules).length === 0) { setError("Invalid grammar. Format: S -> aS | b"); return; }
      // ── CFG validation: each LHS must be exactly one symbol (no spaces) ──
      const lines = grammarText.trim().split("\n");
      for (const line of lines) {
        const parts = line.split("->");
        if (parts.length < 2) continue;
        const lhs = parts[0].trim();
        // A single symbol can be multi-char (e.g. "Expr") but must contain no whitespace
        if (!lhs || lhs.includes(" ")) {
          setIsCFG(false); setNonCFGRule(lhs + " \u2192 " + parts.slice(1).join("->").trim());
          setLmdSteps([]); setRmdSteps([]); setTreeRules(null); setTreeStart(null); setTreeTarget(""); setGenerated(true); return;
        }
      }
      // ── Variable set V = all LHS symbols ──
      const variables = Object.keys(rules);
      if (variables.length === 0) {
        setError("Invalid grammar: No variables (non-terminals) found.");
        return;
      }
      // ── Terminal set Σ = RHS symbols not in V, ignoring ε ──
      const terminals = new Set();
      for (const alts of Object.values(rules)) {
        for (const alt of alts) {
          // tokenize: space-separated if spaces present, else char-by-char
          const syms = alt.trim().includes(" ")
            ? alt.trim().split(/\s+/).filter(Boolean)
            : alt.trim().split("").filter(s => s.trim() !== "");
          for (const sym of syms) {
            if (sym !== "ε" && !variables.includes(sym)) terminals.add(sym);
          }
        }
      }
      if (terminals.size === 0) {
        setError("Invalid grammar: No terminal symbols found. Every RHS must contain at least one terminal.");
        return;
      }
      setDetectedSets({ variables, terminals: [...terminals] });

      // ── Case-sensitivity validation ──────────────────────────────────────────
      // Rule: LHS symbols (non-terminals) must be uppercase to distinguish from
      // terminals (lowercase). Scan every variable and every RHS-only symbol.
      const caseErrors   = [];   // hard — block derivation
      const caseWarnings = [];   // soft — allow derivation but inform user

      for (const v of variables) {
        // Any LHS symbol where every character is lowercase (a–z) is a hard error.
        // This covers both single-char ("s") and multi-char ("expr") lowercase variables.
        if (/^[a-z]+$/.test(v)) {
          caseErrors.push(
            `Error: Variable "${v}" detected in lowercase. ` +
            `According to formal grammar theory, Non-Terminals (Variables) must be ` +
            `Uppercase letters (A–Z) to distinguish them from Terminals (a–z). ` +
            `Please capitalize your variables: "${v}" → "${v.toUpperCase()}".`
          );
        } else if (/[a-z]/.test(v[0]) && v.length > 1) {
          // Mixed-case multi-char names (e.g. "expr1", "eXPR") — warn, don't block
          caseWarnings.push(
            `Warning: Variable "${v}" starts with a lowercase letter. ` +
            `By convention, non-terminals begin with an uppercase letter ` +
            `(e.g. "${v[0].toUpperCase() + v.slice(1)}"). ` +
            `This may cause ambiguity with terminal symbols.`
          );
        }
      }
      // Warn about uppercase symbols that appear ONLY in RHS (never defined as LHS)
      for (const t of terminals) {
        if (/^[A-Z]$/.test(t)) {
          caseWarnings.push(
            `Warning: Symbol "${t}" is uppercase but never appears as a Left-Hand Side variable. ` +
            `Uppercase symbols are conventionally Non-Terminals — did you forget to define a production for "${t}"?`
          );
        }
      }

      if (caseErrors.length > 0 || caseWarnings.length > 0) {
        setCaseIssues({ errors: caseErrors, warnings: caseWarnings });
      }
      // Hard errors block all derivation
      if (caseErrors.length > 0) {
        setGenerated(true); return;
      }
      // ─────────────────────────────────────────────────────────────────────────
      const start = Object.keys(rules)[0];
      const tgt = targetStr.replace(/\s/g, "").split("");
      const lmd = deriveSteps(rules, start, tgt, "lmd");
      const rmd = deriveSteps(rules, start, tgt, "rmd");
      setLmdSteps(lmd); setRmdSteps(rmd);
      setTreeRules(rules); setTreeStart(start); setTreeTarget(targetStr.replace(/\s/g, ""));
      // Compute parse tree stats immediately so all stats update on Generate click
      try {
        const pr = buildParseTree(rules, start, targetStr.replace(/\s/g, ""));
        const trees = (pr && pr.allTrees) ? pr.allTrees : [];
        setParseTreeCount(trees.length);
        setIsAmbiguous(trees.length > 1);
      } catch(e2) { setParseTreeCount(0); setIsAmbiguous(false); }
      if (lmd.length === 0) {
        const info = analyzeDerivationFailure(rules, start, targetStr.replace(/\s/g, ""));
        setFailureInfo(info);
        const autoStr = generateValidString(rules, start, Math.max(2, targetStr.replace(/\s/g, "").length));
        setAutoGenStr(autoStr);
      }
      setGenerated(true); setAnimationKey(k => k + 1);
    } catch (e) { setError("Error: " + e.message); }
  }, [grammarText, targetStr]);

  useEffect(() => { generate(); }, []);

  const nts = treeRules ? new Set(Object.keys(treeRules)) : new Set();
  const stepsToShow = activeTab === "lmd" ? lmdSteps : rmdSteps;
  const mode = activeTab === "lmd" ? "lmd" : "rmd";

  const examples = [
    { label: "aⁿbⁿ",             grammar: "S -> aSb | ab",                                         str: "aaabbb"  },
    { label: "Balanced",          grammar: "S -> SS | aSb | ab",                                     str: "aabb"    },
    { label: "Left Recursion",    grammar: "E -> E+T | T\nT -> T*F | F\nF -> a | b",                str: "a+b"     },
    { label: "Right Recursion",   grammar: "S -> aS | bS | a | b",                                   str: "aba"     },
    { label: "Palindrome",        grammar: "S -> aSa | bSb | a | b | ε",                             str: "abba"    },
    { label: "aⁿb²ⁿ",            grammar: "S -> aSbb | abb",                                         str: "aabbbb"  },
    { label: "Ambiguous Expr ⚡", grammar: "E -> E+E | E*E | E-E | a | b | c",                      str: "a+b*c"   },
    { label: "Dangling Else ⚡",   grammar: "S -> iS | iSeS | a",                                     str: "iia"     },
    { label: "Dyck Words",        grammar: "S -> SS | (S) | ε",                                      str: "(())"    },
    { label: "Even Length",       grammar: "S -> aSa | bSb | aSb | bSa | aa | bb | ab | ba",        str: "abba"    },
    { label: "aⁿbⁿcⁿ-like",      grammar: "S -> aSBC | aBC\nCB -> BC\naB -> ab\nbB -> bb\nbC -> bc\ncC -> cc", str: "abc" },
  ];

  return (
    <div style={{ minHeight: "100vh", background: "#030712", color: "#e2e8f0", position: "relative", fontFamily: "'Inter','Segoe UI',sans-serif" }}>
      <GridBackground />
      <style>{`
        @import url('https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&family=JetBrains+Mono:wght@400;500;600&display=swap');
        * { box-sizing:border-box; }
        /* ── token colours ── */
        .t-nt   { color:#93c5fd; font-weight:700; }
        .t-term { color:#4ade80; font-weight:700; }
        .t-active { color:#1c1917; font-weight:800;
                    background:linear-gradient(135deg,#fef08a,#fbbf24);
                    border-radius:5px; padding:2px 6px;
                    box-shadow:0 0 10px rgba(251,191,36,0.6),0 0 0 2px rgba(251,191,36,0.25);
                    position:relative; }
        /* legacy – kept so any stray usages don't break */
        .step-row { display:flex; align-items:flex-start; gap:8px; padding:8px 12px; border-radius:8px;
                    background:rgba(30,41,59,0.5); margin-bottom:6px; font-family:'JetBrains Mono',monospace;
                    border:1px solid rgba(99,102,241,0.08); transition:background 0.2s; flex-wrap:wrap; }
        .step-row:hover { background:rgba(49,46,129,0.25); }

        /* ── panel shell ── */
        .nb-panel  { background:#080e1c; border:1px solid rgba(99,102,241,0.25); border-radius:18px; overflow:hidden; }
        .nb-header { display:flex; justify-content:space-between; align-items:center;
                     padding:14px 22px 13px; border-bottom:1px solid rgba(99,102,241,0.15);
                     background:rgba(15,23,42,0.9); flex-wrap:wrap; gap:8px; }
        .nb-title      { font-size:clamp(13px,1.8vw,17px); font-weight:700; }
        .nb-step-count { font-size:clamp(11px,1.3vw,13px); color:#6f757c; font-family:'JetBrains Mono'; }
        .nb-body { padding:20px 22px 18px; }

        /* ── unified step card ── */
        .nb-card {
          display:flex; align-items:stretch; gap:0;
          margin-bottom:8px;
          border-radius:12px; overflow:hidden;
          border:1px solid rgba(99,102,241,0.13);
          transition:border-color 0.2s, box-shadow 0.2s;
        }
        .nb-card:hover { border-color:rgba(139,92,246,0.35); box-shadow:0 2px 16px rgba(99,102,241,0.08); }
        .nb-card.card-last { border-color:rgba(74,222,128,0.28); }
        .nb-card.card-last:hover { border-color:rgba(74,222,128,0.5); box-shadow:0 2px 16px rgba(74,222,128,0.08); }

        /* left gutter: step index + arrow stacked */
        .nb-gutter {
          display:flex; flex-direction:column; align-items:center; justify-content:center;
          min-width:54px; padding:10px 6px; gap:4px; flex-shrink:0;
          background:rgba(99,102,241,0.07); border-right:1px solid rgba(99,102,241,0.12);
        }
        .nb-card.card-last .nb-gutter { background:rgba(74,222,128,0.06); border-right-color:rgba(74,222,128,0.15); }
        .nb-gutter-idx  { font-family:'JetBrains Mono'; font-size:clamp(9px,1.05vw,11px);
                          color:#475569; font-weight:600; letter-spacing:0.04em; user-select:none; }
        .nb-gutter-arr  { font-family:'JetBrains Mono'; font-size:clamp(15px,1.8vw,19px);
                          color:#6366f1; line-height:1; }
        .nb-card.card-last .nb-gutter-arr { color:#4ade80; }

        /* centre: rule pill (action) + sentential form (result) */
        .nb-centre { display:flex; flex-direction:column; justify-content:center; flex:1; padding:9px 14px; gap:6px; background:rgba(15,23,42,0.55); }
        .nb-card.card-last .nb-centre { background:rgba(9,28,18,0.6); }

        .nb-action-row { display:flex; align-items:center; gap:6px; }
        .nb-action-icon { font-size:10px; color:#7c3aed; }
        .nb-action-text {
          font-family:'JetBrains Mono'; font-size:clamp(9px,1.05vw,11px);
          color:#a78bfa; background:rgba(109,40,217,0.15);
          border:1px solid rgba(139,92,246,0.28);
          border-radius:20px; padding:2px 10px;
          white-space:nowrap; letter-spacing:0.02em;
        }
        .nb-action-text .ar-nt  { color:#c4b5fd; font-weight:700; }
        .nb-action-text .ar-rhs { color:#e9d5ff; }

        .nb-result-row { display:flex; align-items:center; flex-wrap:wrap; gap:3px; }
        .nb-sym { font-family:'JetBrains Mono'; font-size:clamp(13px,1.6vw,17px); font-weight:700; display:inline-block; }

        /* ── connector arrow between cards ── */
        .nb-connector { text-align:center; color:rgba(99,102,241,0.35); font-size:16px;
                        margin:-2px 0; line-height:1; user-select:none; padding-left:26px; }

        /* ── yield bar ── */
        .nb-yield-bar {
          margin-top:14px; padding:14px 18px;
          background:linear-gradient(135deg,rgba(16,57,32,0.85),rgba(5,46,22,0.9));
          border:1px solid rgba(74,222,128,0.35); border-radius:12px;
          display:flex; align-items:center; gap:12px; flex-wrap:wrap;
        }
        .nb-yield-badge {
          font-family:'JetBrains Mono'; font-size:clamp(9px,1.05vw,11px); font-weight:800;
          letter-spacing:0.12em; text-transform:uppercase;
          color:#052e16; background:linear-gradient(135deg,#4ade80,#22c55e);
          border-radius:20px; padding:3px 12px; flex-shrink:0;
        }
        .nb-yield-eq { font-family:'JetBrains Mono'; font-size:clamp(12px,1.4vw,15px); color:#6b7280; }
        .nb-yield-str { font-family:'JetBrains Mono'; font-size:clamp(14px,1.7vw,18px);
                        font-weight:800; color:#86efac; letter-spacing:0.06em; word-break:break-all; }
        .nb-yield-len { margin-left:auto; font-family:'JetBrains Mono';
                        font-size:clamp(10px,1.1vw,12px); color:#4ade80; opacity:0.8; }
        textarea, input[type=text] { background:rgba(15,23,42,0.95); border:1px solid rgba(99,102,241,0.2); border-radius:10px; color:#e2e8f0; font-family:'JetBrains Mono',monospace; font-size:clamp(12px,1.5vw,14px); padding:12px; width:100%; outline:none; transition:border-color 0.2s; resize:vertical; }
        textarea:focus, input[type=text]:focus { border-color:rgba(139,92,246,0.5); box-shadow:0 0 0 3px rgba(139,92,246,0.08); }
        .tab-btn { background:rgba(99,102,241,0.08); color:#94a3b8; border:1px solid rgba(99,102,241,0.18); padding:8px 14px; border-radius:8px; font-size:clamp(12px,1.5vw,15px); cursor:pointer; font-family:inherit; transition:all 0.2s; white-space:nowrap; }
        .tab-btn:hover { background:rgba(99,102,241,0.15); color:#e2e8f0; }
        .tab-btn.active { background:rgba(139,92,246,0.2); border-color:#8b5cf6; color:#c084fc; }
        .ex-btn { background:rgba(99,102,241,0.08); color:#94a3b8; border:1px solid rgba(99,102,241,0.15); padding:5px 10px; border-radius:6px; font-size:clamp(11px,1.3vw,13px); cursor:pointer; font-family:'JetBrains Mono',monospace; transition:all 0.2s; }
        .ex-btn:hover { background:rgba(99,102,241,0.18); color:#a5b4fc; }
        .gen-btn { background:linear-gradient(135deg,#6366f1,#8b5cf6); color:white; border:none; padding:13px; border-radius:10px; font-size:clamp(14px,1.8vw,17px); font-weight:700; cursor:pointer; width:100%; transition:all 0.3s; font-family:inherit; letter-spacing:0.02em; }
        .gen-btn:hover { opacity:0.9; box-shadow:0 0 24px rgba(139,92,246,0.35); }
        .back-btn { background:rgba(99,102,241,0.1); color:#94a3b8; border:1px solid rgba(99,102,241,0.2); padding:8px 16px; border-radius:8px; font-size:clamp(12px,1.5vw,14px); cursor:pointer; font-family:inherit; transition:all 0.2s; white-space:nowrap; }
        .back-btn:hover { background:rgba(99,102,241,0.2); color:#e2e8f0; }
        ::-webkit-scrollbar { width:5px; height:5px; } ::-webkit-scrollbar-track { background:#0f172a; } ::-webkit-scrollbar-thumb { background:#334155; border-radius:3px; }
        .tool-grid { display:grid; grid-template-columns:min(380px,38%) 1fr; gap:18px; align-items:start; }
        @media (max-width:768px) { .tool-grid { grid-template-columns:1fr; } .tool-nav-links { display:none !important; } .hamburger { display:none !important; } .nav-interactive-label { display:none !important; } }
        @media (min-width:769px) { .hamburger { display:none !important; } }
        .prod-rule-badge { font-size:clamp(9px,1.1vw,11px); color:#c084fc; background:rgba(139,92,246,0.12); border:1px solid rgba(139,92,246,0.22); padding:2px 7px; border-radius:4px; white-space:nowrap; font-family:'JetBrains Mono',monospace; margin-top:2px; }
        @keyframes statPop { 0%{transform:scale(0.88);opacity:0} 60%{transform:scale(1.05)} 100%{transform:scale(1);opacity:1} }
      `}</style>

      <nav style={{ position: "sticky", top: 0, zIndex: 100, background: "transparent", backdropFilter: "blur(20px)", borderBottom: "1px solid rgba(99,102,241,0.15)", padding: "0 20px" }}>
        <div style={{ margin: "0 auto", display: "flex", alignItems: "center", justifyContent: "space-between", height: 56, position: "relative" }}>
          <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
            <button className="back-btn" onClick={onBack}>← Back</button>
            <div style={{ width: 1, height: 20, background: "rgba(99,102,241,0.2)" }} />
            <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
              <div style={{ width: 26, height: 26, borderRadius: 7, background: "linear-gradient(135deg,#6366f1,#8b5cf6)", display: "flex", alignItems: "center", justifyContent: "center", fontSize: 13, fontWeight: 800, color: "white" }}>G</div>
              <span style={{ fontSize: "clamp(14px,2vw,17px)", fontWeight: 700, color: "#a5b4fc" }}>CFG Visualiser</span>
              <span style={{ fontSize: 14, color: "#6f757c" }}>/ Generator</span>
            </div>
          </div>
          <div className="nav-interactive-label" style={{ fontSize: 16, color: "#6f757c", fontFamily: "'JetBrains Mono',monospace" }}>Interactive Tool</div>
          <button className="hamburger" onClick={() => setMenuOpen(o => !o)} style={{ background: "rgba(99,102,241,0.1)", border: "1px solid rgba(99,102,241,0.2)", borderRadius: 8, padding: "6px 10px", cursor: "pointer", color: "#94a3b8", fontSize: 18 }}>
            {menuOpen ? "✕" : "☰"}
          </button>
        </div>
      </nav>

      <div style={{ position: "relative", zIndex: 1, margin: "0 auto", padding: "clamp(16px,3vw,32px) clamp(12px,3vw,28px) 60px" }}>
        <div style={{ marginBottom: 22 }}>
          <div style={{ fontSize: "clamp(11px,1.5vw,14px)", letterSpacing: "0.12em", textTransform: "uppercase", color: "#818cf8", fontWeight: 700, marginBottom: 4 }}>Interactive</div>
          <h1 style={{ fontSize: "clamp(22px,4vw,32px)", fontWeight: 800, color: "#f1f5f9", letterSpacing: "-0.02em", marginBottom: 4 }}>CFG Generator</h1>
          <p style={{ color: "#6f757c", fontSize: "clamp(12px,1.5vw,15px)" }}>Enter grammar rules and a target string to generate derivation steps and a parse tree.</p>
        </div>

        <div className="tool-grid">
          {/* LEFT PANEL */}
          <div style={{ background: "rgba(15,23,42,0.92)", border: "1px solid rgba(99,102,241,0.2)", borderRadius: 16, padding: "clamp(14px,2vw,22px)" }}>
            <div style={{ marginBottom: 14 }}>
              <label style={{ display: "block", fontSize: "clamp(11px,1.3vw,14px)", fontWeight: 700, color: "#818cf8", letterSpacing: "0.1em", textTransform: "uppercase", marginBottom: 7 }}>Grammar Rules</label>
              <textarea id="grammar-input" rows={5} value={grammarText} onChange={(e) => setGrammarText(e.target.value)} placeholder={"S -> aSb | ab\nA -> aA | a"} />
              <div style={{ display: "flex", gap: 7, marginTop: 8 }}>
                {[{ label: "→", value: " -> " }, { label: "|", value: " | " }, { label: "ε", value: "ε" }].map((sym) => (
                  <button key={sym.label} onClick={() => {
                    const el = document.getElementById("grammar-input");
                    const s = el.selectionStart, e2 = el.selectionEnd;
                    const before = grammarText.substring(0, s), after = grammarText.substring(e2);
                    setGrammarText(before + sym.value + after);
                    setTimeout(() => { el.focus(); el.setSelectionRange(s + sym.value.length, s + sym.value.length); }, 0);
                  }} style={{ background: "rgba(99,102,241,0.15)", border: "1px solid rgba(99,102,241,0.3)", borderRadius: 6, color: "#a5b4fc", padding: "4px 11px", fontSize: "clamp(12px,1.4vw,14px)", cursor: "pointer", fontWeight: "bold", transition: "all 0.2s" }}
                    onMouseEnter={(e) => e.target.style.background = "rgba(99,102,241,0.25)"}
                    onMouseLeave={(e) => e.target.style.background = "rgba(99,102,241,0.15)"}>
                    {sym.label}
                  </button>
                ))}
              </div>
              <div style={{ fontSize: "clamp(10px,1.2vw,13px)", color: "#6f757c", marginTop: 6 }}>One rule per line | Use helper buttons for special symbols</div>
            </div>
            <div style={{ marginBottom: 14 }}>
              <label style={{ display: "block", fontSize: "clamp(11px,1.3vw,14px)", fontWeight: 700, color: "#818cf8", letterSpacing: "0.1em", textTransform: "uppercase", marginBottom: 7 }}>Target String</label>
              <input type="text" value={targetStr} onChange={(e) => setTargetStr(e.target.value)} placeholder="aaabbb" style={{ height: 40 }} />
            </div>
            <button className="gen-btn" onClick={generate} style={{ boxShadow: "2px 2px 10px #8b56f6" }}>Generate ↗</button>
            {error && <div style={{ marginTop: 10, color: "#f87171", fontSize: "clamp(11px,1.3vw,13px)", background: "rgba(220,38,38,0.1)", border: "1px solid rgba(220,38,38,0.2)", borderRadius: 8, padding: "8px 12px" }}>{error}</div>}
            <div style={{ marginTop: 16, borderTop: "1px solid rgba(99,102,241,0.1)", paddingTop: 13 }}>
              <div style={{ fontSize: "clamp(12px,1.4vw,15px)", color: "#FFF", marginBottom: 7, fontWeight: 700, letterSpacing: "0.05em", textTransform: "uppercase" }}>Quick Examples</div>
              <div style={{ display: "flex", flexWrap: "wrap", gap: 5 }}>
                {examples.map(ex => (
                  <button key={ex.label} className="ex-btn" onClick={() => { setGrammarText(ex.grammar); setTargetStr(ex.str); }}>{ex.label}</button>
                ))}
              </div>
            </div>
          </div>

          {/* RIGHT PANEL */}
          <div>
            {/* Legend + Stats */}
            <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 12, marginBottom: 14 }}>
              <div style={{ background: "rgba(15,23,42,0.85)", border: "1px solid rgba(99,102,241,0.14)", borderRadius: 12, padding: "12px 16px" }}>
                <div style={{ fontSize: "clamp(13px,1.4vw,15px)", color: "#FFF", marginBottom: 10, fontWeight: 700, letterSpacing: "0.05em", textTransform: "uppercase" }}>Parse Tree Legend</div>
                {[
                  { c: "#dc2626", bd: "#b91c1c", l: "Start Symbol", desc: "Root of the tree" },
                  { c: "#2563eb", bd: "#1d4ed8", l: "Non-Terminal", desc: "Expandable variable" },
                  { c: "#16a34a", bd: "#15803d", l: "Terminal", desc: "Final leaf node" }
                ].map(({ c, bd, l, desc }) => (
                  <div key={l} style={{ display: "flex", alignItems: "center", gap: 10, marginBottom: 8 }}>
                    <span style={{ width: 17, height: 17, borderRadius: "50%", background: c, border: `2px solid ${bd}`, display: "inline-block", flexShrink: 0 }} />
                    <div>
                      <div style={{ fontSize: "clamp(17px,1.8vw,14px)", color: "#818cf8", fontWeight: 600, lineHeight: 1.9 }}>{l}</div>
                      <div style={{ fontSize: "clamp(11px,1.3vw,13px)", color: "#7b838a", lineHeight: 1.5 }}>{desc}</div>
                    </div>
                  </div>
                ))}
              </div>
              <div style={{ background: "rgba(15,23,42,0.85)", border: "1px solid rgba(99,102,241,0.14)", borderRadius: 12, padding: "12px 16px" }}>
                <div style={{ fontSize: "clamp(11px,1.3vw,14px)", color: "#FFF", marginBottom: 8, fontWeight: 700, letterSpacing: "0.05em", textTransform: "uppercase" }}>Stats</div>
                <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 7 }}>
                  {[
                    { l: "LMD Steps", v: lmdSteps.length, c: "#818cf8" },
                    { l: "RMD Steps", v: rmdSteps.length, c: "#4ade80" },
                    { l: "Productions", v: treeRules ? Object.keys(treeRules).length : 0, c: "#c084fc" },
                    { l: "Target Length", v: targetStr.replace(/\s/g, "").length, c: "#38bdf8" },
                    { l: "Parse Trees", v: parseTreeCount, c: parseTreeCount > 1 ? "#fb923c" : "#818cf8" },
                    { l: "Ambiguous", v: isAmbiguous ? "YES" : "NO", c: isAmbiguous ? "#fb923c" : "#4ade80", isText: true },
                  ].map(s => (
                    <div key={s.l} style={{ background: (s.l === "Ambiguous" || s.l === "Parse Trees") && isAmbiguous ? "rgba(251,146,60,0.07)" : "rgba(99,102,241,0.06)", borderRadius: 7, padding: "8px 10px", border: (s.l === "Ambiguous" || s.l === "Parse Trees") && isAmbiguous ? "1px solid rgba(251,146,60,0.28)" : "1px solid rgba(99,102,241,0.1)", transition: "all 0.4s" }}>
                      <div style={{ fontSize: "clamp(13px,1.7vw,18px)", fontWeight: 700, marginBottom: 1 }}>
                        {s.isText
                          ? <span style={{ color: s.c, fontFamily: "'JetBrains Mono'", fontWeight: 700 }}>{s.v}</span>
                          : <AnimatedCount value={s.v} color={s.c} />}
                      </div>
                      <div style={{ fontSize: "clamp(9px,1.1vw,12px)", color: "#6f757c", marginTop: 1 }}>{s.l}</div>
                    </div>
                  ))}
                </div>
              </div>
            </div>

            {/* Tabs */}
            <div style={{ display: "flex", gap: 8, marginBottom: 14, flexWrap: "wrap" }}>
              {[
                { id: "lmd", label: "← Leftmost" },
                { id: "rmd", label: "Rightmost →" },
                { id: "tree", label: isAmbiguous ? `⬡ Parse Trees (${parseTreeCount})` : "⬡ Parse Tree" }
              ].map(tab => (
                <button key={tab.id} className={`tab-btn ${activeTab === tab.id ? "active" : ""}`} onClick={() => setActiveTab(tab.id)}
                  style={{ fontWeight: 700, ...(tab.id === "tree" && isAmbiguous ? { borderColor: activeTab === tab.id ? "#fb923c" : "rgba(251,146,60,0.4)", color: activeTab === tab.id ? "#fb923c" : undefined } : {}) }}>
                  {tab.label}
                </button>
              ))}
            </div>

            {/* Non-CFG Warning */}
            {generated && !isCFG && (
              <div style={{ background: "rgba(220,38,38,0.08)", border: "1px solid rgba(220,38,38,0.35)", borderRadius: 12, padding: "16px 20px", marginBottom: 14 }}>
                <div style={{ display: "flex", alignItems: "center", gap: 10, marginBottom: 8 }}>
                  <span style={{ fontSize: 18, color: "#f87171" }}>⚠</span>
                  <span style={{ fontSize: "clamp(13px,1.6vw,15px)", fontWeight: 700, color: "#f87171", textTransform: "uppercase" }}>Not a Context-Free Grammar</span>
                </div>
                <p style={{ fontSize: "clamp(11px,1.3vw,13px)", color: "#94a3b8", marginBottom: 10, lineHeight: 1.6 }}>
                  A CFG requires every production to have <strong style={{ color: "#fca5a5" }}>exactly one non-terminal</strong> on the LHS. This grammar has a multi-symbol LHS, making it a <strong style={{ color: "#fca5a5" }}>Context-Sensitive Grammar (CSG)</strong>.
                </p>
                <div style={{ fontFamily: "'JetBrains Mono',monospace", fontSize: "clamp(12px,1.4vw,14px)", display: "flex", alignItems: "center", gap: 8, background: "rgba(220,38,38,0.1)", borderRadius: 8, padding: "8px 12px" }}>
                  <span style={{ color: "#f87171", fontWeight: 700, fontSize: 16 }}>⇒</span>
                  <span style={{ color: "#fca5a5" }}>{nonCFGRule}</span>
                  <span style={{ color: "#6b7280", fontSize: 11, marginLeft: 4 }}>(invalid CFG rule)</span>
                </div>
              </div>
            )}

            {/* Case-Sensitivity Formal Explanation Panel */}
            {generated && caseIssues && (
              <div style={{ marginBottom: 14 }}>
                {/* Hard errors */}
                {caseIssues.errors.length > 0 && (
                  <div style={{ background: "rgba(220,38,38,0.08)", border: "1px solid rgba(220,38,38,0.38)", borderRadius: 12, padding: "16px 20px", marginBottom: 10 }}>
                    <div style={{ display: "flex", alignItems: "center", gap: 10, marginBottom: 10 }}>
                      <span style={{ fontSize: 18 }}>🚫</span>
                      <span style={{ fontSize: "clamp(13px,1.6vw,15px)", fontWeight: 700, color: "#f87171", textTransform: "uppercase", letterSpacing: "0.06em" }}>Lowercase Variable Detected — Derivation Blocked</span>
                    </div>
                    {caseIssues.errors.map((msg, i) => {
                      // Split into the "Error: Variable X" headline and the rest
                      const colonIdx = msg.indexOf(". ");
                      const headline = colonIdx !== -1 ? msg.slice(0, colonIdx + 1) : msg;
                      const detail   = colonIdx !== -1 ? msg.slice(colonIdx + 2)    : "";
                      return (
                        <div key={i} style={{ background: "rgba(220,38,38,0.07)", border: "1px solid rgba(220,38,38,0.18)", borderRadius: 8, padding: "10px 14px", marginBottom: i < caseIssues.errors.length - 1 ? 8 : 0 }}>
                          <div style={{ fontFamily: "'JetBrains Mono',monospace", fontSize: "clamp(11px,1.3vw,13px)", color: "#f87171", fontWeight: 700, marginBottom: 4 }}>{headline}</div>
                          <div style={{ fontSize: "clamp(11px,1.25vw,13px)", color: "#94a3b8", lineHeight: 1.65 }}>{detail}</div>
                        </div>
                      );
                    })}
                  </div>
                )}
                {/* Soft warnings */}
                {caseIssues.warnings.length > 0 && (
                  <div style={{ background: "rgba(251,146,60,0.07)", border: "1px solid rgba(251,146,60,0.32)", borderRadius: 12, padding: "14px 18px" }}>
                    <div style={{ display: "flex", alignItems: "center", gap: 10, marginBottom: 10 }}>
                      <span style={{ fontSize: 16 }}>⚠️</span>
                      <span style={{ fontSize: "clamp(12px,1.5vw,14px)", fontWeight: 700, color: "#fb923c", textTransform: "uppercase", letterSpacing: "0.06em" }}>Convention Warnings</span>
                    </div>
                    {caseIssues.warnings.map((msg, i) => (
                      <div key={i} style={{ fontFamily: "'JetBrains Mono',monospace", fontSize: "clamp(10px,1.2vw,12px)", color: "#fdba74", lineHeight: 1.7, marginBottom: i < caseIssues.warnings.length - 1 ? 6 : 0, paddingLeft: 6, borderLeft: "2px solid rgba(251,146,60,0.3)" }}>
                        {msg}
                      </div>
                    ))}
                  </div>
                )}
              </div>
            )}

            {/* Detected Grammar Sets V and Σ */}
            {generated && detectedSets && isCFG && !caseIssues?.errors?.length && (
              <div style={{ background: "rgba(99,102,241,0.06)", border: "1px solid rgba(99,102,241,0.2)", borderRadius: 10, padding: "10px 14px", marginBottom: 14, fontFamily: "'JetBrains Mono',monospace", fontSize: "clamp(11px,1.3vw,13px)", display: "flex", gap: 18, flexWrap: "wrap", alignItems: "center" }}>
                <span style={{ color: "#6b7280" }}>Detected:</span>
                <span><span style={{ color: "#818cf8", fontWeight: 700 }}>V</span><span style={{ color: "#475569" }}> = </span><span style={{ color: "#a5b4fc" }}>{"{" + detectedSets.variables.join(", ") + "}"}</span></span>
                <span><span style={{ color: "#4ade80", fontWeight: 700 }}>Σ</span><span style={{ color: "#475569" }}> = </span><span style={{ color: "#86efac" }}>{"{" + detectedSets.terminals.join(", ") + "}"}</span></span>
              </div>
            )}

            {/* LMD / RMD Notebook Tab */}
            {(activeTab === "lmd" || activeTab === "rmd") && isCFG && (
              <div className="nb-panel">
                {/* ── Notebook header ── */}
                <div className="nb-header">
                  <div style={{ display:"flex", alignItems:"center", gap:10 }}>
                    
                    <div>
                      <div className="nb-title" style={{ color: activeTab==="lmd" ? "#a5b4fc" : "#4ade80" }}>
                        {activeTab==="lmd" ? "← Leftmost Derivation" : "Rightmost Derivation →"}
                      </div>
                      <div style={{ fontSize:"clamp(10px,1.1vw,12px)", color:"#8a8d94", fontFamily:"'JetBrains Mono'", marginTop:2 }}>
                        {activeTab==="lmd" ? "Always expand the leftmost non-terminal first" : "Always expand the rightmost non-terminal first"}
                      </div>
                    </div>
                  </div>
                  <div style={{ display:"flex", alignItems:"center", gap:10 }}>
                    {/* Color key */}
                    <div style={{ 
  display: "flex", 
  gap: "16px", 
  alignItems: "center", 
  fontSize: "clamp(9px, 1.05vw, 11px)", 
  fontFamily: "'JetBrains Mono'", 
  flexWrap: "wrap",
  padding: "10px"
}}>
  {/* Yellow Box (No text, just the box) */}
  <span style={{ display: "flex", alignItems: "center", gap: "6px" }}>
    <span style={{ 
      background: "linear-gradient(135deg, #fde68a, #fbbf24)", 
      borderRadius: "3px", 
      width: "16px", 
      height: "16px", 
      display: "inline-block" 
    }}></span>
    <span style={{ color: "#FFF",fontSize:"12px" }}>Active NT</span>
  </span>

  {/* Blue Circle (B) */}
  <span style={{ display: "flex", alignItems: "center", gap: "6px" }}>
    <span style={{ 
      color: "#1e1b4b", 
      background: "#93c5fd", 
      fontWeight: 800, 
      width: "18px", 
      height: "18px", 
      borderRadius: "50%", 
      display: "flex", 
      alignItems: "center", 
      justifyContent: "center"
    }}></span>
    <span style={{ color: "#FFF",fontSize:"12px" }}> Non-Terminal</span>
  </span>

  {/* Green Circle (a) */}
  <span style={{ display: "flex", alignItems: "center", gap: "6px" }}>
    <span style={{ 
      color: "#064e3b", 
      background: "#4ade80", 
      fontWeight: 800, 
      width: "18px", 
      height: "18px", 
      borderRadius: "50%", 
      display: "flex", 
      alignItems: "center", 
      justifyContent: "center",
    }}></span>
    <span style={{ color: "#FFF",fontSize:"12px" }}> Terminal</span>
  </span>
</div>
                    <div className="nb-step-count">{stepsToShow.length > 0 ? `${stepsToShow.length - 1} step${stepsToShow.length !== 2 ? "s" : ""}` : "—"}</div>
                  </div>
                </div>

                {/* ── Notebook body ── */}
                <div className="nb-body">
                  {stepsToShow.length === 0 ? (
                    <div>
                      {generated && failureInfo ? (
                        <div style={{ background: "rgba(220,38,38,0.06)", border: "1px solid rgba(220,38,38,0.2)", borderRadius: 10, padding: "16px 18px" }}>
                          <div style={{ display: "flex", alignItems: "center", gap: 10, marginBottom: 10 }}>
                            <span style={{ fontSize: 20 }}>
                              {failureInfo.reason === "unreachable" ? "🔗" : failureInfo.reason === "stuck_nt" ? "🔒" : "❌"}
                            </span>
                            <span style={{ color: "#f87171", fontWeight: 700, fontSize: "clamp(12px,1.5vw,15px)" }}>
                              {failureInfo.reason === "unreachable" ? "Unreachable Non-Terminal Detected" :
                                failureInfo.reason === "stuck_nt" ? `Unproductive Non-Terminal: "${failureInfo.stuckNT}"` :
                                  failureInfo.reason === "mismatch" ? `Mismatch at Position ${failureInfo.mismatchPos + 1}` :
                                    "String Not Derivable from This Grammar"}
                            </span>
                          </div>
                          <p style={{ color: "#94a3b8", fontSize: "clamp(11px,1.3vw,13px)", lineHeight: 1.7, marginBottom: 14 }}>{failureInfo.details}</p>
                          {failureInfo.mismatchPos >= 0 && treeTarget && (
                            <div style={{ fontFamily: "'JetBrains Mono',monospace", fontSize: "clamp(12px,1.4vw,14px)", marginBottom: 14, background: "rgba(15,23,42,0.6)", borderRadius: 7, padding: "10px 14px" }}>
                              <div style={{ fontSize: 11, color: "#475569", marginBottom: 5 }}>Target string — failure point highlighted:</div>
                              <span style={{ color: "#4ade80" }}>{treeTarget.slice(0, failureInfo.mismatchPos)}</span>
                              <span style={{ color: "#f87171", background: "rgba(220,38,38,0.25)", borderRadius: 3, padding: "1px 5px", border: "1px solid rgba(220,38,38,0.4)" }}>{treeTarget[failureInfo.mismatchPos] || "∅"}</span>
                              <span style={{ color: "#475569" }}>{treeTarget.slice(failureInfo.mismatchPos + 1)}</span>
                              <span style={{ color: "#6b7280", marginLeft: 10, fontSize: 11 }}>← fails here</span>
                            </div>
                          )}
                          <div style={{ borderTop: "1px solid rgba(220,38,38,0.15)", paddingTop: 14 }}>
                            <div style={{ fontSize: "clamp(11px,1.3vw,13px)", color: "#818cf8", fontWeight: 600, marginBottom: 10 }}>🔧 Auto-Generate a Valid String</div>
                            <div style={{ display: "flex", gap: 6, alignItems: "center", flexWrap: "wrap", marginBottom: 10 }}>
                              <span style={{ color: "#6f757c", fontSize: 12 }}>Length:</span>
                              {[2, 3, 4, 5, 6, 8].map(n => (
                                <button key={n} onClick={() => setAutoGenStr(generateValidString(treeRules, treeStart, n) || "—")}
                                  style={{ background: "rgba(99,102,241,0.12)", border: "1px solid rgba(99,102,241,0.25)", borderRadius: 5, color: "#a5b4fc", padding: "3px 10px", fontSize: 12, cursor: "pointer", fontFamily: "'JetBrains Mono',monospace", transition: "all 0.2s" }}
                                  onMouseEnter={e => e.target.style.background = "rgba(99,102,241,0.22)"}
                                  onMouseLeave={e => e.target.style.background = "rgba(99,102,241,0.12)"}>
                                  {n}
                                </button>
                              ))}
                              <button onClick={() => setAutoGenStr(generateValidString(treeRules, treeStart, 0) || "—")}
                                style={{ background: "rgba(99,102,241,0.12)", border: "1px solid rgba(99,102,241,0.25)", borderRadius: 5, color: "#a5b4fc", padding: "3px 10px", fontSize: 12, cursor: "pointer", fontFamily: "'JetBrains Mono',monospace" }}>
                                any
                              </button>
                            </div>
                            {autoGenStr !== null && (
                              <div style={{ display: "flex", alignItems: "center", gap: 10, flexWrap: "wrap" }}>
                                <span style={{ fontSize: 12, color: "#6f757c" }}>Result:</span>
                                {!autoGenStr || autoGenStr === "—" ? (
                                  <span style={{ color: "#f87171", fontFamily: "'JetBrains Mono'", fontSize: 13 }}>Not possible for this length</span>
                                ) : (
                                  <>
                                    <code style={{ color: "#4ade80", fontFamily: "'JetBrains Mono'", fontSize: 14, background: "rgba(74,222,128,0.08)", border: "1px solid rgba(74,222,128,0.22)", borderRadius: 6, padding: "3px 12px" }}>{autoGenStr}</code>
                                    <button onClick={() => setTargetStr(autoGenStr)} style={{ background: "linear-gradient(135deg,#6366f1,#8b5cf6)", color: "white", border: "none", borderRadius: 6, padding: "4px 12px", fontSize: 12, fontWeight: 700, cursor: "pointer", fontFamily: "inherit" }}>Use This ↗</button>
                                  </>
                                )}
                              </div>
                            )}
                          </div>
                        </div>
                      ) : generated ? (
                        <div style={{ textAlign: "center", padding: "24px 0" }}>
                          <div style={{ fontSize: 28, marginBottom: 8 }}>∅</div>
                          <div style={{ color: "#f87171", fontSize: "clamp(12px,1.5vw,14px)", fontWeight: 600 }}>String not derivable</div>
                        </div>
                      ) : (
                        <div style={{ color: "#475569", textAlign: "center", padding: "32px 0", fontSize: "clamp(12px,1.5vw,15px)" }}>Click Generate to compute derivation steps</div>
                      )}
                    </div>
                  ) : (() => {
                    // ── pre-compute metadata for every transition ──────────────────
                    // metas[i] describes the rule applied TO REACH step i
                    const metas = stepsToShow.map((_, i) =>
                      i === 0 ? null : getProductionMeta(stepsToShow, i, treeRules || {}, mode)
                    );
                    const finalStep = stepsToShow[stepsToShow.length - 1];
                    const yieldStr  = finalStep && finalStep.every(s => !nts.has(s)) ? finalStep.join("") : null;

                    // activeSymIdx[i] = position in step[i] of the NT about to be expanded
                    // (i.e. the NT that metas[i+1] will consume)
                    const activeSymIdx = stepsToShow.map((_, i) => {
                      const nextMeta = i < stepsToShow.length - 1 ? metas[i + 1] : null;
                      return nextMeta ? nextMeta.activeIdx : -1;
                    });

                    return (
                      <>
                        {stepsToShow.map((step, i) => {
                          const meta   = metas[i];          // rule that produced THIS step
                          const isLast = i === stepsToShow.length - 1;
                          const aIdx   = activeSymIdx[i];   // which sym in THIS step fires next

                          // ── gutter labels ──
                          const arrLabel = i === 0 ? "⊢" : "⇒";

                          return (
                            <div key={i}>
                              {/* ── connector dot between cards (skip before first) ── */}
                              {i > 0 && <div className="nb-connector">╎</div>}

                              {/* ═══════════ UNIFIED STEP CARD ═══════════ */}
                              <div className={`nb-card${isLast && yieldStr ? " card-last" : ""}`}>

                                {/* LEFT GUTTER: arrow */}
                                <div className="nb-gutter">
                                  <span className="nb-gutter-arr">{arrLabel}</span>
                                </div>

                                {/* CENTRE: action row (rule pill) + result row (sentential form) */}
                                <div className="nb-centre">

                                  {/* ── ACTION ROW: rule pill sits above the result ── */}
                                  {meta ? (
                                    <div className="nb-action-row">
                                      <span className="nb-action-icon">▶</span>
                                      <span className="nb-action-text">
                                        Apply&nbsp;
                                        <span className="ar-nt">{meta.expandedNT}</span>
                                        &nbsp;→&nbsp;
                                        <span className="ar-rhs">{meta.rhs || "ε"}</span>
                                      </span>
                                    </div>
                                  ) : (
                                    /* step 0: no rule applied, just a "start" label */
                                    <div className="nb-action-row">
                                      <span className="nb-action-icon">◉</span>
                                      <span className="nb-action-text" style={{ color:"#94a3b8", background:"rgba(71,85,105,0.18)", borderColor:"rgba(100,116,139,0.25)" }}>
                                        Start symbol
                                      </span>
                                    </div>
                                  )}

                                  {/* ── RESULT ROW: sentential form with active-symbol highlight ── */}
                                  <div className="nb-result-row">
                                    {step.map((sym, j) => {
                                      const isActive = j === aIdx && !isLast;
                                      const isNT     = nts.has(sym);
                                      return (
                                        <span
                                          key={j}
                                          className={`nb-sym${isActive ? " t-active" : isNT ? " t-nt" : " t-term"}`}
                                          title={isActive ? `"${sym}" will be expanded in the next step` : isNT ? "Non-Terminal" : "Terminal"}
                                        >
                                          {sym}
                                        </span>
                                      );
                                    })}
                                  </div>

                                </div>{/* /nb-centre */}
                              </div>{/* /nb-card */}
                            </div>
                          );
                        })}

                        {/* ══════════ YIELD BAR ══════════ */}
                        {yieldStr && (
                          <div className="nb-yield-bar">
                            <span className="nb-yield-badge">Yield</span>
                            <span className="nb-yield-eq">w&nbsp;=</span>
                            <span className="nb-yield-str">{yieldStr}</span>
                            <span className="nb-yield-len">|w|&nbsp;=&nbsp;{yieldStr.length}</span>
                          </div>
                        )}
                      </>
                    );
                  })()}
                </div>
              </div>
            )}

            {/* Parse Tree Tab */}
            {activeTab === "tree" && (
              <div style={{ background: "rgba(15,23,42,0.85)", border: isAmbiguous ? "1px solid rgba(251,146,60,0.3)" : "1px solid rgba(99,102,241,0.14)", borderRadius: 14, padding: "clamp(14px,2vw,24px)", transition: "border-color 0.4s" }}>
                <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: 16, flexWrap: "wrap", gap: 8 }}>
                  <div style={{ fontSize: "clamp(15px,2vw,20px)", fontWeight: 700, color: isAmbiguous ? "#fb923c" : "#c084fc", display: "flex", alignItems: "center", gap: 8 }}>
                    Parse Tree
                    {isAmbiguous && <span style={{ fontSize: 12, fontWeight: 600, background: "rgba(251,146,60,0.15)", border: "1px solid rgba(251,146,60,0.3)", borderRadius: 5, padding: "2px 8px" }}>⚡ {parseTreeCount} trees</span>}
                  </div>
                  {treeTarget && <div style={{ fontSize: "clamp(11px,1.3vw,14px)", color: "#fff", fontFamily: "'JetBrains Mono'" }}>yield: <span style={{ color: "#4ade80" }}>{treeTarget}</span></div>}
                </div>
                {treeRules && treeStart ? (
                  <ParseTreeSVG rules={treeRules} startSymbol={treeStart} targetStr={treeTarget} animationKey={animationKey}
                    onAmbiguityInfo={(amb, count) => { setIsAmbiguous(amb); setParseTreeCount(count); }} />
                ) : (
                  <div style={{ color: "#475569", textAlign: "center", padding: "40px 0", fontSize: "clamp(12px,1.5vw,15px)" }}>Click Generate to build the parse tree</div>
                )}
              </div>
            )}
          </div>
        </div>
      </div>
    </div>
  );
}
// ─── HOME PAGE ─────────────────────────────────────────────────────────────────
export default function CFGApp() {
  const [page, setPage] = useState("home");
  const [activeSection, setActiveSection] = useState("concept");
  const [fade, setFade] = useState(false);
  const [grammar, setGrammar] = useState("S -> aSb | ab");
  const [target, setTarget] = useState("aaabbb");
  const [active, setActive] = useState(false);
  const [homeMenuOpen, setHomeMenuOpen] = useState(false);

  const rules = parseGrammar(grammar);
  const start = Object.keys(rules)[0];

  useEffect(() => {
    if (page !== "home") return;
    const ids = ["concept","derivations","trees","ambiguity","applications"];
    const obs = new IntersectionObserver(
      (entries) => { entries.forEach(e => { if (e.isIntersecting) setActiveSection(e.target.id); }); },
      { threshold: 0.35, rootMargin: "-5% 0px -50% 0px" }
    );
    ids.forEach(id => { const el = document.getElementById(id); if (el) obs.observe(el); });
    return () => obs.disconnect();
  }, [page]);

  const goTool = () => { setFade(true); setTimeout(() => { setPage("tool"); setFade(false); }, 380); };
  const goHome = () => { setFade(true); setTimeout(() => { setPage("home"); setFade(false); }, 380); };

  if (page === "tool") return (
    <div style={{ opacity: fade ? 0 : 1, transition: "opacity 0.38s ease" }}>
      <ToolPage onBack={goHome}/>
    </div>
  );

  return (
    <div style={{ opacity:fade?0:1, transition:"opacity 0.38s ease", background:"#030712", color:"#e2e8f0", minHeight:"100vh", fontFamily:"'Inter','Segoe UI',sans-serif", position:"relative" }}>
      <style>{`
        @import url('https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700;800&family=JetBrains+Mono:wght@400;500;600&display=swap');
        * { box-sizing:border-box; margin:0; padding:0; }
        ::-webkit-scrollbar { width:6px; } ::-webkit-scrollbar-track { background:#0f172a; } ::-webkit-scrollbar-thumb { background:#334155; border-radius:3px; }
        .glow-text { background:linear-gradient(135deg,#818cf8 0%,#c084fc 50%,#38bdf8 100%); -webkit-background-clip:text; -webkit-text-fill-color:transparent; background-clip:text; }

        .nav-link { cursor:pointer; font-size:11.5px; letter-spacing:0.07em; padding:6px 13px; border-radius:20px; transition:all 0.22s; color:#64748b; text-transform:uppercase; font-weight:700; border:none; background:none; position:relative; }
        .nav-link:hover { color:#94a3b8; background:rgba(99,102,241,0.1); }
        .nav-link.active { color:#c084fc; background:rgba(139,92,246,0.14); border:1px solid rgba(139,92,246,0.22); }

        .launch-nav { cursor:pointer; font-size:11.5px; letter-spacing:0.07em; padding:7px 20px; border-radius:20px; font-weight:800; text-transform:uppercase; border:none; position:relative; overflow:hidden; background:linear-gradient(135deg,#6366f1,#8b5cf6); color:white; box-shadow:0 0 16px rgba(139,92,246,0.3); transition:all 0.3s; }
        .launch-nav:hover { transform:translateY(-1px); box-shadow:0 0 28px rgba(139,92,246,0.5); }
        .launch-nav::after { content:''; position:absolute; inset:0; background:linear-gradient(135deg,#818cf8,#a78bfa); opacity:0; transition:opacity 0.3s; }
        .launch-nav:hover::after { opacity:1; }
        .launch-nav span { position:relative; z-index:1; }
        .home-hamburger { display:none; background:rgba(99,102,241,0.1); border:1px solid rgba(99,102,241,0.2); borderRadius:8px; padding:6px 10px; cursor:pointer; color:#94a3b8; fontSize:18px; }
        .home-nav-links { display:flex; align-items:center; gap:4px; }
        @media (max-width: 700px) {
          .home-hamburger { display:block !important; }
          .home-nav-links { display:none !important; }
          .home-nav-links.open { display:flex !important; flex-direction:column; align-items:flex-start; position:absolute; top:100%; left:0; right:0; background:rgba(3,7,18,0.98); border-bottom:1px solid rgba(99,102,241,0.2); padding:12px 20px; gap:6px; z-index:200; }
        }

        .card-glow { border:1px solid rgba(99,102,241,0.18); background:rgba(15,23,42,0.82); border-radius:16px; padding:26px; transition:border-color 0.3s,transform 0.3s,box-shadow 0.3s; }
        .card-glow:hover { border-color:rgba(139,92,246,0.42); transform:translateY(-3px); box-shadow:0 8px 32px rgba(99,102,241,0.1); }

        .btn-hero { background:linear-gradient(135deg,#6366f1,#8b5cf6,#7c3aed); color:white; border:none; padding:15px 36px; border-radius:50px; font-size:15px; font-weight:800; cursor:pointer; transition:all 0.3s; font-family:inherit; min-width:220px; text-align:center; }
        .btn-hero:hover { transform:translateY(-2px); box-shadow:0 0 36px rgba(139,92,246,0.45); }
        .btn-outline { background:transparent; color:#94a3b8; border:1px solid rgba(99,102,241,0.3); padding:15px 36px; border-radius:50px; font-size:15px; cursor:pointer; transition:all 0.2s; font-family:inherit; font-weight:500; min-width:220px; text-align:center; }
        .btn-outline:hover { border-color:rgba(139,92,246,0.5); color:#c084fc; background:rgba(99,102,241,0.07); }

        .step-demo { display:flex; align-items:flex-start; gap:8px; padding:9px 14px; border-radius:8px; background:rgba(30,41,59,0.55); margin-bottom:6px; font-family:'JetBrains Mono',monospace; font-size:13px; border:1px solid rgba(99,102,241,0.08); flex-wrap:wrap; }
        .nt { color:#818cf8; font-weight:700; }
        .term { color:#4ade80; font-weight:700; }

        .app-card { background:rgba(15,23,42,0.88); border:1px solid rgba(99,102,241,0.12); border-radius:14px; padding:24px; transition:all 0.3s; }
        .app-card:hover { border-color:rgba(139,92,246,0.4); background:rgba(30,27,75,0.4); transform:translateY(-3px); box-shadow:0 8px 28px rgba(99,102,241,0.1); }

        .badge { font-size:11px; letter-spacing:0.15em; text-transform:uppercase; color:#818cf8; font-weight:700; margin-bottom:12px; display:inline-block; }
        .derive-col { background:rgba(15,23,42,0.75); border-radius:14px; padding:22px; border:1px solid rgba(99,102,241,0.1); flex:1; min-width:280px; }
        .footer-link { color:#475569; font-size:13px; transition:color 0.2s; cursor:pointer; display:block; margin-bottom:9px; }
        .footer-link:hover { color:#a5b4fc; }
        .ambig-box { background:rgba(220,38,38,0.06); border:1px solid rgba(220,38,38,0.2); border-radius:12px; padding:24px; }
        @media (max-width: 600px) {
          .ambig-grid { grid-template-columns: 1fr !important; }
          .footer-grid { grid-template-columns: 1fr 1fr !important; gap: 24px !important; }
          .footer-brand { grid-column: 1 / -1 !important; }
          .footer-bottom { flex-direction: column !important; align-items: flex-start !important; gap: 8px !important; }
          .btn-hero, .btn-outline { min-width: 0 !important; width: 100%; }
        }
        @media (max-width: 420px) {
          .footer-grid { grid-template-columns: 1fr !important; }
        }

        /* Mini live-preview strip in hero */
        .hero-chip { display:inline-flex; align-items:center; gap:6px; background:rgba(99,102,241,0.09); border:1px solid rgba(99,102,241,0.18); border-radius:8px; padding:4px 11px; font-family:'JetBrains Mono',monospace; font-size:12px; color:#64748b; }
        .hero-chip .hl { color:#818cf8; font-weight:700; }
        .hero-chip .hl2 { color:#4ade80; font-weight:700; }
      `}</style>

      <GridBackground />

      {/* ── NAVBAR ── */}
      <nav style={{ position:"sticky", top:0, zIndex:100, background:"transparent", backdropFilter:"blur(20px)", borderBottom:"1px solid rgba(99,102,241,0.12)", padding:"10px 32px" }}>
        <div style={{ margin:"0 auto", display:"flex", alignItems:"center", justifyContent:"space-between", height:62, position:"relative" }}>
          <div style={{ display:"flex", alignItems:"center", gap:10 }}>
            <div style={{ width:34, height:34, borderRadius:9, background:"linear-gradient(135deg,#6366f1,#8b5cf6)", display:"flex", alignItems:"center", justifyContent:"center", fontSize:17, fontWeight:800, color:"white" }}>G</div>
            <span style={{ fontSize:20, fontWeight:800, color:"#e2e8f0", letterSpacing:"-0.01em" }}>
              CFG <span style={{ color:"#818cf8" }}>Visualiser</span>
            </span>
          </div>
          <div className={`home-nav-links${homeMenuOpen ? " open" : ""}`} onClick={() => setHomeMenuOpen(false)}>
            {[
              { id:"concept",      l:"Concept"      },
              { id:"derivations",  l:"Derivations"  },
              { id:"trees",        l:"Trees"        },
              { id:"ambiguity",    l:"Ambiguity"    },
              { id:"applications", l:"Applications" },
            ].map(({ id, l }) => (
              <button key={id} className={`nav-link ${activeSection === id ? "active" : ""}`}
                onClick={() => { document.getElementById(id)?.scrollIntoView({ behavior:"smooth" }); setActiveSection(id); }} style={{fontSize:14}}>
                {l}
              </button>
            ))}
            {/* <div style={{ width:1, height:22, background:"rgba(99,102,241,0.18)", margin:"0 8px" }}/> */}
            <button className="launch-nav" onClick={goTool}><span style={{fontWeight:300, fontSize:14}}>Launch Tool</span></button>
          </div>
          <button className="home-hamburger" onClick={() => setHomeMenuOpen(o => !o)} style={{ display:"none", background:"rgba(99,102,241,0.1)", border:"1px solid rgba(99,102,241,0.2)", borderRadius:8, padding:"6px 10px", cursor:"pointer", color:"#94a3b8", fontSize:18 }}>
            {homeMenuOpen ? "✕" : "☰"}
          </button>
        </div>
      </nav>

      <div style={{ position:"relative", zIndex:1 }}>

        {/* ── HERO ── */}
        <section style={{ maxWidth:1100, margin:"0 auto", padding:"110px 32px 80px", textAlign:"center" }}>
          <Reveal>
            <h1 style={{ fontSize:"clamp(44px,7vw,82px)", fontWeight:800, lineHeight:1.04, letterSpacing:"-0.04em", marginBottom:24 }}>
              <span className="glow-text">Master Context-Free</span>
              <br/><span style={{ color:"#f1f5f9" }}>Grammar</span>
            </h1>
            <p style={{ fontSize:18, color:"#94a3b8", maxWidth:560, margin:"0 auto 44px", lineHeight:1.7 }}>
              Visualize derivations, parse trees, and the formal mathematics of context-free languages — step by step.
            </p>
            <div style={{ display:"flex", gap:14, justifyContent:"center", flexWrap:"wrap" }}>
              <button className="btn-hero" onClick={goTool}>Launch CFG Generator</button>
              <button className="btn-outline" onClick={() => document.getElementById("concept")?.scrollIntoView({ behavior:"smooth" })}>Explore Theory</button>
            </div>
          </Reveal>


          
        </section>

        {/* ── CONCEPT ── */}
        <section id="concept" style={{ margin:"0 auto", padding:"60px 32px" }}>
          <Reveal style={{margin:"0 auto 24px",textAlign:"center" }}>
            <span className="badge" style={{fontSize:18}}>01 — Concept</span>
            <h2 style={{ fontSize:40, fontWeight:800, letterSpacing:"-0.03em", marginBottom:10, color:"#f1f5f9" }}>The Formal Definition</h2>
            <p style={{ color:"#64748b", fontSize:20, marginBottom:48}}>A context-free grammar is a 4-tuple. Each component plays a precise mathematical role in generating a language.</p>
          </Reveal>

          <Reveal delay={200}>
            <div style={{ marginTop:56, display:"flex", justifyContent:"center", overflowX:"auto", padding:"0 4px" }}>
              <div style={{ display:"inline-flex", alignItems:"center", gap:8, background:"rgba(99,102,241,0.07)", border:"1px solid rgba(99,102,241,0.2)", borderRadius:16, padding:"14px 24px", fontFamily:"'JetBrains Mono',monospace", fontSize:"clamp(15px,3.5vw,18px)", color:"#a5b4fc", letterSpacing:"0.04em", flexWrap:"nowrap", whiteSpace:"nowrap", justifyContent:"center", overflowX:"auto", maxWidth:"100%" }}>
                <span>G&nbsp;=&nbsp;{"{ "}</span>
                <span style={{ color:"#818cf8" }}>V</span><span style={{ color:"#475569" }}>,</span>
                <span style={{ color:"#34d399" }}>&nbsp;Σ</span><span style={{ color:"#475569" }}>,</span>
                <span style={{ color:"#f59e0b" }}>&nbsp;S</span><span style={{ color:"#475569" }}>,</span>
                <span style={{ color:"#f472b6" }}>&nbsp;P</span><span>&nbsp;{"}"}</span>
              </div>
            </div>
          </Reveal>

          {/* Mini grammar preview chips */}
          <Reveal delay={350}>
            <div style={{ marginTop:32, display:"flex", justifyContent:"center", gap:10, flexWrap:"wrap" ,}}>
              {[
                { rule:"S", arrow:"→", rhs:"aSb | ab" },
                { rule:"E", arrow:"→", rhs:"E+T | T" },
                { rule:"S", arrow:"→", rhs:"SS | ε" },
              ].map((c,i) => (
                <div key={i} className="hero-chip">
                  <span className="hl" style={{ fontSize:18 }}>{c.rule}</span>
                  <span style={{ color:"#334155" ,fontSize:18}}>{c.arrow}</span>
                  <span className="hl2" style={{ fontSize:18 }}>{c.rhs}</span>
                </div>
              ))}
            </div>
          </Reveal>
          <br></br>
          {/* Parent Grid */}
<div style={{ display: "grid", gridTemplateColumns: "repeat(auto-fit, minmax(240px, 1fr))", gap: 18, marginTop: 32, gridAutoRows: "1fr" }}>
  {[
    { sym: "V", c: "#818cf8", bg: "rgba(99,102,241,0.1)", bd: "rgba(99,102,241,0.28)", title: "Variables", sub: "Non-Terminals", desc: "These are abstract placeholders, usually capitalized, that generate strings by being replaced via production rules.", eg: "S, A, B, E, T" },
    { sym: "Σ", c: "#34d399", bg: "rgba(52,211,153,0.1)", bd: "rgba(52,211,153,0.28)", title: "Terminals", sub: "Alphabet", desc: "The actual characters that appear in the final string. These are the atoms of the language — irreducible symbols.", eg: "a, b, 0, 1, +, *" },
    { sym: "S", c: "#f59e0b", bg: "rgba(245,158,11,0.1)", bd: "rgba(245,158,11,0.28)", title: "Start Symbol", sub: "Axiom", desc: "The root non-terminal from which every valid string in the language is derivable. All derivations begin here.", eg: "Always S by convention" },
    { sym: "P", c: "#f472b6", bg: "rgba(244,114,182,0.1)", bd: "rgba(244,114,182,0.28)", title: "Productions", sub: "Rewriting Rules", desc: "Rules of the form A → α, where α is any sequence of terminals and non-terminals. The engine of grammar.", eg: "S → aSb | ab" },
  ].map((card, i) => (
    <Reveal key={card.sym} delay={i * 75} style={{ display: "flex", height: "100%" }}> {/* 1. Force Reveal to take full height */}
      <div 
        className="card-glow" 
        style={{ 
          borderColor: card.bd, 
          display: "flex",          // 2. Make card a flexbox
          flexDirection: "column",  // 3. Stack items vertically
          height: "100%",           // 4. Fill the Reveal wrapper
          width: "100%" 
        }}
      >
        <div style={{ width: 52, height: 52, borderRadius: 13, background: card.bg, border: `1px solid ${card.bd}`, display: "flex", alignItems: "center", justifyContent: "center", fontFamily: "'JetBrains Mono'", fontSize: 26, color: card.c, fontWeight: 800, marginBottom: 18 }}>
          {card.sym}
        </div>
        <div style={{ fontSize: 20, color: card.c, fontWeight: 700, letterSpacing: "0.1em", textTransform: "uppercase", marginBottom: 5 }}>
          {card.sub}
        </div>
        <h3 style={{ fontSize: 20, fontWeight: 700, color: "#f1f5f9", marginBottom: 10 }}>
          {card.title}
        </h3>
        
        {/* 5. flex-grow: 1 pushes the code block to the bottom of the card */}
        <p style={{ fontSize: 20, color: "#64748b", lineHeight: 1.65, marginBottom: 14, flexGrow: 1 }}>
          {card.desc}
        </p>
        
        <code style={{ fontSize: 20, color: card.c, fontFamily: "'JetBrains Mono'" }}>
          eg. {card.eg}
        </code>
      </div>
    </Reveal>
  ))}
</div>

          {/* Production rule format strip */}
          <Reveal delay={200}>
            <div style={{ marginTop:20, background:"rgba(15,23,42,0.7)", border:"1px solid rgba(99,102,241,0.12)", borderRadius:12, padding:"16px 20px", display:"flex", alignItems:"center", gap:16, flexWrap:"wrap", margin:"20px auto 0", justifyContent:"center", textAlign:"center" }}>
              <span style={{ fontSize:"clamp(14px,3vw,22px)", color:"#FFFFFF", fontWeight:700, letterSpacing:"0.08em", textTransform:"uppercase", whiteSpace:"nowrap" }}>Production Rule Format</span>
              <div style={{ fontFamily:"'JetBrains Mono'", fontSize:"clamp(13px,3vw,20px)", display:"flex", alignItems:"center", gap:6, flexWrap:"wrap", justifyContent:"center" }}>
                <span style={{ color:"#f472b6", fontWeight:700 }}>A</span>
                <span style={{ color:"#475569" }}>→</span>
                <span style={{ color:"#a5b4fc" }}>α</span>
                <span style={{ color:"#FFFFFF" }}>where α ∈ (V ∪ Σ)* and A ∈ V</span>
              </div>
            </div>
          </Reveal>
        </section>

        <br></br>
        <br></br>

        {/* ── DERIVATIONS ── */}
        <section id="derivations" style={{ margin:"0 auto", padding:"60px 32px" }}>
          <Reveal style={{margin:"0 auto 24px",textAlign:"center"}}>
            <span className="badge" style={{fontSize:18}}>02 — Derivations</span>
            <h2 style={{ fontSize:40, fontWeight:800, letterSpacing:"-0.03em", marginBottom:10, color:"#f1f5f9" }}>The Art of Derivation</h2>
            <p style={{ color:"#64748b", fontSize:20, marginBottom:48 }}>A derivation transforms the start symbol into a terminal string through ordered production rule applications.</p>
          </Reveal>
          <div style={{ display:"flex", gap:22, flexWrap:"wrap" }}>
            {[
              {
                label:"LEFTMOST", dir:"← LMD",
                pillBg:"rgba(37,99,235,0.15)", pillC:"#60a5fa", pillBd:"rgba(37,99,235,0.3)",
                rule:"Replace the leftmost non-terminal at every step. String builds left to right.",
                steps:[
                  { s:"S",    r:"Start" },
                  { s:"AB",   r:"S → AB" },
                  { s:"aAB",  r:"A → aA  (leftmost A)" },
                  { s:"aaB",  r:"A → a   (leftmost A)" },
                  { s:"aab",  r:"B → b" },
                ]
              },
              {
                label:"RIGHTMOST", dir:"RMD →",
                pillBg:"rgba(22,163,74,0.15)", pillC:"#4ade80", pillBd:"rgba(22,163,74,0.3)",
                rule:"Replace the rightmost non-terminal at every step. String builds right to left.",
                steps:[
                  { s:"S",    r:"Start" },
                  { s:"AB",   r:"S → AB" },
                  { s:"Ab",   r:"B → b   (rightmost B)" },
                  { s:"aAb",  r:"A → aA  (rightmost A)" },
                  { s:"aab",  r:"A → a" },
                ]
              },
            ].map((col, ci) => (
              <Reveal key={col.label} delay={ci * 80} style={{ flex:1 }}>
                <div className="derive-col">
                  <div style={{ display:"flex", alignItems:"center", gap:10, marginBottom:14 }}>
                    <span style={{ display:"inline-flex", alignItems:"center", padding:"3px 10px", borderRadius:20, fontSize:22, fontWeight:700, background:col.pillBg, color:col.pillC, border:`1px solid ${col.pillBd}` }}>{col.dir}</span>
                    <span style={{ fontSize:22, fontWeight:700, color:"#f1f5f9" }}>{col.label} DERIVATION</span>
                  </div>
                  <p style={{ fontSize:20, color:"#64748b", marginBottom:18, lineHeight:1.6 }}>{col.rule}</p>
                  <div style={{ fontSize:20, color:"#b5bcc5", fontFamily:"'JetBrains Mono'", marginBottom:12 }}>
                    G: S → AB, A → aA | a, B → b   <br></br>Target: <span style={{ color:"#4ade80" }}>aab</span>
                  </div>
                  <div style={{ borderTop:"1px solid rgba(99,102,241,0.1)", paddingTop:12 ,}}>
                    {col.steps.map((step, i) => (
                      <div key={i} className="step-demo">
                        <span style={{ color:"#b5bcc5", fontSize:"clamp(14px,3vw,20px)", minWidth:20 }}>{i === 0 ? "⊢" : "→"}</span>
                        <span style={{ flex:1, fontSize:"clamp(13px,3vw,20px)", letterSpacing:"0.03em" }}>
                          {step.s.split("").map((ch, j) => (
                            <span key={j} className={["A","B","S","C","D","E","T","F"].includes(ch) ? "nt" : "term"}>{ch}</span>
                          ))}
                        </span>
                        <span style={{ fontSize:"clamp(11px,2.5vw,16px)", color:"#8d9299", wordBreak:"break-word", textAlign:"right" }}>{step.r}</span>
                      </div>
                    ))}
                  </div>
                </div>
              </Reveal>
            ))}
          </div>
        </section>

        <br></br>
        <br></br>

        {/* ── TREES ── */}
        <section id="trees" style={{ margin:"0 auto", padding:"60px 32px" }}>
          <Reveal style={{margin:"0 auto 24px",textAlign:"center"}}>
            <span className="badge" style={{fontSize:18}}>03 — Parse Trees</span>
            <h2 style={{ fontSize:40, fontWeight:800, letterSpacing:"-0.03em", marginBottom:10, color:"#f1f5f9" }}>Tree Visualization</h2>
            <p style={{ color:"#64748b", fontSize:20, marginBottom:40 }}>A parse tree is the graphical form of a derivation. <br></br> The final string obtained by concatenating the labels of all the leaf nodes in order from left to right.</p>
          </Reveal>
          <div style={{ display:"grid", gridTemplateColumns:"repeat(auto-fit,minmax(200px,1fr))", gap:16, marginBottom:36 }}>
            {[
              { sym:"●", c:"#f87171", t:"Root Node",     d:"Always the Start Symbol (S)" },
              { sym:"●", c:"#60a5fa", t:"Interior Nodes", d:"Non-terminals — expandable" },
              { sym:"●", c:"#4ade80", t:"Leaf Nodes",     d:"Terminals — the final string" },
              { sym:"→", c:"#c084fc", t:"Yield",          d:"Left-to-right leaf concatenation" },
            ].map((item, i) => (
              <Reveal key={item.t} delay={i * 60}>
                <div className="card-glow" style={{ padding:20, textAlign:"center" }}>
                  <div style={{ fontSize:26, color:item.c, marginBottom:10 }}>{item.sym}</div>
                  <div style={{ fontSize:20, fontWeight:700, color:"#f1f5f9", marginBottom:6 }}>{item.t}</div>
                  <div style={{ fontSize:20, color:"#64748b" }}>{item.d}</div>
                </div>
              </Reveal>
            ))}
          </div>
          <Reveal delay={120}>
  <div style={{ margin: "0 auto", width: "fit-content", background: "rgba(15,23,42,0.85)", border: "1px solid rgba(99,102,241,0.15)", borderRadius: 16, padding: 28 }}>
    <div style={{ fontSize: 20, color: "#b0b0b0", marginBottom: 18 }}>
      <span style={{ color: "white" }}>Example Visualisation</span> <br />
      <br />
      <code style={{ color: "#818cf8", fontFamily: "'JetBrains Mono'" }}>S → aSb | ab</code> <br />
      Target: <code style={{ color: "#4ade80", fontFamily: "'JetBrains Mono'" }}>aaabbb</code>
    </div>
    
    {/* Tree Area */}
    <div style={{ overflowX: "auto", display: "flex", justifyContent: "center", background: "rgba(2, 6, 23, 0.4)", borderRadius: 12, padding: "20px" }}>
      <ParseTreeSVG 
        rules={{ "S": ["aSb", "ab"] }} 
        startSymbol="S" 
        targetStr="aaabbb" 
      />
    </div>

    {/* Legend (Colors) */}
    <div style={{ marginTop: 20, display: "flex", gap: 18, flexWrap: "wrap", justifyContent: "center", borderTop: "1px solid rgba(255,255,255,0.05)", paddingTop: 16 }}>
      {[
        { c: "#ef4444", l: "Start Symbol" }, // Red
        { c: "#3b82f6", l: "Non-Terminal" }, // Blue
        { c: "#22c55e", l: "Terminal" }      // Green
      ].map(l => (
        <div key={l.l} style={{ display: "flex", alignItems: "center", gap: 8, fontSize: 13, color: "#94a3b8" }}>
          <span style={{ width: 12, height: 12, borderRadius: "50%", background: l.c, display: "inline-block" }} />
          {l.l}
        </div>
      ))}
    </div>
  </div>
</Reveal>
        </section>

        <br></br>
        <br></br>

        {/* ── AMBIGUITY ── */}
        <section id="ambiguity" style={{ margin:"0 auto", padding:"20px 32px 60px" }}>
          <Reveal style={{margin:"0 auto", textAlign:"center"}}>
            <span className="badge" style={{fontSize:18}}>04 — Ambiguity</span>
            <h2 style={{ fontSize:40, fontWeight:800, letterSpacing:"-0.03em", marginBottom:10, color:"#f1f5f9" }}>The Ambiguity Trap</h2>
            <p style={{ color:"#64748b", fontSize:20, marginBottom:40 }}>
              A grammar is <strong style={{ color:"#f87171" }}>ambiguous</strong> when a single string admits two or more distinct parse trees — a critical issue in compiler design.
            </p>
          </Reveal>
          <Reveal delay={80}>
            <div className="ambig-box">
              <div style={{ fontSize:20, fontWeight:700, color:"#fca5a5", marginBottom:12 }}>⚠ Example: <br></br><br></br><span style={{color:"#FFF"}}>S → S+S | S*S | a | b</span></div>
              <div style={{ fontSize:22, color:"#94a3b8", marginBottom:16 }}>
                The string <code style={{ color:"#f87171", fontFamily:"'JetBrains Mono'" }}>a+a*b</code> yields two different leftmost derivations:
              </div>
              <div style={{ display:"grid", gridTemplateColumns:"1fr 1fr", gap:14 }} className="ambig-grid">
                {[
                  { l:"Derivation 1 (+ root)", c:"#f87171", steps:["S → S+S","→ a+S","→ a+S*S","→ a+a*S","→ a+a*b"] },
                  { l:"Derivation 2 (* root)", c:"#fb923c", steps:["S → S*S","→ S+S*S","→ a+S*S","→ a+a*S","→ a+a*b"] },
                ].map(d => (
                  <div key={d.l} style={{ background:"rgba(15,23,42,0.5)", borderRadius:10, padding:14, border:`1px solid ${d.c}22` }}>
                    <div style={{ fontSize:20, fontWeight:700, color:d.c, marginBottom:10 }}>{d.l}</div>
                    {d.steps.map((s, i) => <div key={i} style={{ fontSize:20, fontFamily:"'JetBrains Mono'", color:"#b5bcc5", padding:"2px 0" }}>{s}</div>)}
                  </div>
                ))}
              </div>
              <div style={{ marginTop:14, fontSize:20, color:"#b5bcc5" }}>
                Both derivations produce the same string but encode different operator precedences — the grammar must be redesigned to eliminate ambiguity.
              </div>
            </div>
          </Reveal>
        </section>

        <br></br>
        <br></br>

        {/* ── APPLICATIONS ── */}
        <section id="applications" style={{ margin:"0 auto", padding:"20px 32px 60px" }}>
          <Reveal style={{margin:"0 auto", textAlign:"center"}}>
            <span className="badge" style={{fontSize:18}}>05 — Applications</span>
            <h2 style={{ fontSize:40, fontWeight:800, letterSpacing:"-0.03em", marginBottom:10, color:"#f1f5f9" }}>Real-World Applications</h2>
            <p style={{ color:"#64748b", fontSize:22, marginBottom:48 }}>Context-free grammars are foundational to computing — from compilers to natural language AI.</p>
          </Reveal>
          <div style={{ display:"grid", gridTemplateColumns:"repeat(auto-fit,minmax(240px,1fr))", gap:18 }}>
            {[
              { icon:"⚙", bg:"rgba(99,102,241,0.14)", c:"#818cf8", title:"Compiler Design",    sub:"Syntax Analysis", desc:"CFG defines the grammar of C++, Java, Python. The parser checks source code against production rules, building an AST or reporting syntax errors.", tag:"Parser · AST · Tokens" },
              { icon:"🧠", bg:"rgba(52,211,153,0.14)", c:"#34d399", title:"Natural Language",  sub:"NLP & AI",        desc:"CFG models sentence structure — Sentence → NP + VP — enabling AI to parse grammatical roles, build syntax trees, and understand language.",  tag:"NLP · Parsing · Syntax" },
              { icon:"🌐", bg:"rgba(251,146,60,0.14)", c:"#fb923c", title:"XML / HTML",         sub:"Document Parsing",desc:"CFG manages nested tag structures, ensuring every opening tag has a matching closing tag. Validates that web documents are well-formed.",          tag:"DOM · Validation · Tags" },
              { icon:"∑", bg:"rgba(244,114,182,0.14)", c:"#f472b6", title:"Math Expressions",  sub:"Operator Precedence", desc:"Grammar rules encode BODMAS/PEMDAS. Multiplication binds deeper in the tree than addition, so 2+3×4 correctly evaluates to 14.",        tag:"BODMAS · Eval · AST" },
            ].map((app, i) => (
              <Reveal key={app.title} delay={i * 70}>
                <div className="app-card">
                  <div style={{ width:48, height:48, borderRadius:12, background:app.bg, display:"flex", alignItems:"center", justifyContent:"center", fontSize:22, color:app.c, marginBottom:14 }}>{app.icon}</div>
                  <div style={{ fontSize:18, color:app.c, fontWeight:700, letterSpacing:"0.1em", textTransform:"uppercase", marginBottom:5 }}>{app.sub}</div>
                  <h3 style={{ fontSize:24, fontWeight:700, color:"#f1f5f9", marginBottom:10 }}>{app.title}</h3>
                  <p style={{ fontSize:18, color:"#64748b", lineHeight:1.65, marginBottom:12 }}>{app.desc}</p>
                  <code style={{ fontSize:20, color:"#b5bcc5", fontFamily:"'JetBrains Mono'" }}>{app.tag}</code>
                </div>
              </Reveal>
            ))}
          </div>
        </section>

        <br></br>
        <br></br>

        {/* ── CTA BAND ── */}
        <section style={{ width:"100%", maxWidth:800, margin:"0 auto", padding:"24px 24px 80px" }}>
          <Reveal style={{ margin:"0 auto", textAlign:"center" }}>
            <div style={{ background:"linear-gradient(135deg,rgba(99,102,241,0.12),rgba(139,92,246,0.15),rgba(59,130,246,0.1))", border:"1px solid rgba(139,92,246,0.22)", borderRadius:24, padding:"56px 40px", textAlign:"center" }}>
              <div style={{ fontSize:18, letterSpacing:"0.15em", textTransform:"uppercase", color:"#818cf8", fontWeight:700, marginBottom:14 }}>Ready to Experiment?</div>
              <h2 style={{ fontSize:36, fontWeight:800, color:"#f1f5f9", marginBottom:14, letterSpacing:"-0.03em" }}>Turn Your Learning Into Practice</h2>
              <p style={{ color:"#64748b", fontSize:20, margin:"0 auto 36px", lineHeight:1.7 }}>Enter any context-free grammar, pick a target string, and watch the derivation unfold step by step.</p>
              <button className="btn-hero" onClick={goTool}>⚡ Launch CFG Generator</button>
            </div>
          </Reveal>
        </section>

        {/* ── FOOTER ── */}
        <footer style={{ borderTop:"1px solid rgba(99,102,241,0.1)", background:"rgba(3,0,0,0.97)", backdropFilter:"blur(20px)", padding:"64px 32px 32px" }}>
          <div style={{ margin:"0 auto" }}>
            <div className="footer-grid" style={{ display:"grid", gridTemplateColumns:"2fr 1fr 1fr 1fr", gap:30, marginBottom:56 }}>
              {/* Brand */}
              <div className="footer-brand">
                <div style={{ display:"flex", alignItems:"center", gap:10, marginBottom:18 }}>
                  <div style={{ width:38, height:38, borderRadius:10, background:"linear-gradient(135deg,#6366f1,#8b5cf6)", display:"flex", alignItems:"center", justifyContent:"center", fontSize:22, fontWeight:800, color:"white" }}>G</div>
                  <span style={{ fontSize:20, fontWeight:800, color:"#e2e8f0" }}>CFG <span style={{ color:"#818cf8" }}>Visualiser</span></span>
                </div>
                <p style={{ fontSize:20, color:"#b5bcc5", lineHeight:1.75, marginBottom:22 }}>
                  An academic-grade interactive platform for studying context-free grammars, formal derivation sequences, and parse tree structures.
                </p>
                <div style={{ display:"flex", gap:8, flexWrap:"wrap" }}>
                  {["Parse trees", "Derivations", "Grammar"].map(tag => (
                    <span key={tag} style={{ fontSize:16, color:"#818cf8", background:"rgba(99,102,241,0.1)", border:"1px solid rgba(99,102,241,0.18)", padding:"3px 10px", borderRadius:20, fontWeight:500, letterSpacing:"0.04em" }}>{tag}</span>
                  ))}
                </div>
              </div>

              {/* Tool */}
              <div>
                <div style={{ fontSize:20, fontWeight:700, letterSpacing:"0.1em", textTransform:"uppercase", color:"#818cf8", marginBottom:18 }}>Tool</div>
                {["CFG Generator", "LMD Derivation", "RMD Derivation", "Parse Tree Builder", "Quick Examples"].map(l => (
                  <span key={l} className="footer-link" onClick={goTool} style={{ fontSize:16}}>{l}</span>
                ))}
              </div>

              {/* Theory */}
              <div>
                <div style={{ fontSize:20, fontWeight:700, letterSpacing:"0.1em", textTransform:"uppercase", color:"#818cf8", marginBottom:18 }}>Theory</div>
                {[
                  ["Formal Definition", "concept"],
                  ["Derivation Steps",  "derivations"],
                  ["Parse Trees",       "trees"],
                  ["Ambiguity",         "ambiguity"],
                  ["Applications",      "applications"],
                ].map(([l, id]) => (
                  <span key={l} className="footer-link" onClick={() => document.getElementById(id)?.scrollIntoView({ behavior:"smooth" })} style={{fontSize:16}}>{l}</span>
                ))}
              </div>

              {/* Concepts */}
              {/* Related Concepts */}
<div>
  <div style={{ fontSize: 20, fontWeight: 700, letterSpacing: "0.1em", textTransform: "uppercase", color: "#818cf8", marginBottom: 18 }}>
    Related Concepts
  </div>
  {[
    { name: "Pushdown Automata", link: "https://en.wikipedia.org/wiki/Pushdown_automaton" },
    { name: "Chomsky Normal Form", link: "https://en.wikipedia.org/wiki/Chomsky_normal_form" },
    { name: "CYK Algorithm", link: "https://en.wikipedia.org/wiki/CYK_algorithm" },
    { name: "LR Parsing", link: "https://en.wikipedia.org/wiki/LR_parser" },
    { name: "Pumping Lemma", link: "https://en.wikipedia.org/wiki/Pumping_lemma_for_context-free_languages" }
  ].map(concept => (
    <span 
      key={concept.name} 
      className="footer-link" 
      style={{ fontSize: 16, cursor: "pointer" }}
      onClick={() => window.open(concept.link, "_blank")}
    >
      {concept.name}
    </span>
  ))}
</div>
            </div>

            {/* Divider with grammar pill */}
            <div style={{ display:"flex", alignItems:"center", gap:16, marginBottom:24 }}>
              <div style={{ flex:1, height:"1px", background:"rgba(99,102,241,0.1)" }}/>
              <div style={{ display:"inline-flex", alignItems:"center", gap:8, background:"rgba(99,102,241,0.07)", border:"1px solid rgba(99,102,241,0.2)", borderRadius:16, padding:"6px 20px", fontFamily:"'JetBrains Mono',monospace", fontSize:14, color:"#a5b4fc", letterSpacing:"0.04em" }}>
                <span style={{ color:"#818cf8", fontWeight:700 }}>V</span><span style={{ color:"#475569" }}>,</span>
                <span style={{ color:"#34d399" }}>Σ</span><span style={{ color:"#475569" }}>,</span>
                <span style={{ color:"#f59e0b" }}>S</span><span style={{ color:"#475569" }}>,</span>
                <span style={{ color:"#f472b6" }}>P</span>
              </div>
              <div style={{ flex:1, height:"1px", background:"rgba(99,102,241,0.1)" }}/>
            </div>

            {/* Bottom bar */}
            <div className="footer-bottom" style={{ display:"flex", justifyContent:"center", alignItems:"center", flexWrap:"wrap", gap:12 }}>
              <div style={{ fontSize:16, color:"#b5b5b5" }}>© 2026 CFG Visualiser</div>
              <div style={{ display:"flex", alignItems:"center", gap:8 }}>
                <div style={{ width:6, height:6, borderRadius:"50%", background:"#4ade80" }}/>
                <span style={{ fontSize:16, color:"#b5b5b5" }}>Built for the study of formal language theory</span>
              </div>
              <div style={{ display:"flex", alignItems:"center", gap:8 }}>
                <div style={{ width:6, height:6, borderRadius:"50%", background:"#4ade80" }}/>
                <span style={{ fontSize:16, color:"#b5b5b5" }}>Made with ❤️ by <span style={{color:"#818cf8"}}>Kashish 2024UCS1671</span></span>
              </div>
            </div>
          </div>
        </footer>
      </div>
    </div>
  );
}
