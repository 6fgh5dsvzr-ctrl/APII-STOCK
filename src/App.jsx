import { useState, useEffect, useRef, useMemo } from 'react';
import {
  Package, Plus, X, Search, AlertTriangle, History, Wrench, Loader2,
  QrCode, Camera, Check, Truck, ClipboardList, ArrowLeft, CircleCheck,
  Droplets, Ban, Keyboard, Undo2, LogOut, UserRound, UserRoundPlus,
  CalendarClock, Mail, Send, BellRing, Briefcase, ChevronDown, ChevronUp, ChevronLeft, ChevronRight, Hammer, Archive, RotateCcw, FileDown, Link2, Shield,
} from 'lucide-react';
import { supabase } from './lib/supabaseClient';

/* ---------------------------------------------------------------
   Générateur de QR code (mode octet, correction M, versions 1-4)
   --------------------------------------------------------------- */
// Minimal QR encoder: byte mode, ECC level M, versions 1-4.
const EXP = new Uint8Array(512), LOG = new Uint8Array(256);
(function () {
  let x = 1;
  for (let i = 0; i < 255; i++) { EXP[i] = x; LOG[x] = i; x <<= 1; if (x & 0x100) x ^= 0x11d; }
  for (let i = 255; i < 512; i++) EXP[i] = EXP[i - 255];
})();
function gmul(a, b) { if (a === 0 || b === 0) return 0; return EXP[LOG[a] + LOG[b]]; }
function genPoly(n) {
  let g = [1];
  for (let i = 0; i < n; i++) {
    const res = new Array(g.length + 1).fill(0);
    for (let j = 0; j < g.length; j++) { res[j] ^= g[j]; res[j + 1] ^= gmul(g[j], EXP[i]); }
    g = res;
  }
  return g;
}
function rsEncode(data, n) {
  const g = genPoly(n);
  const res = new Uint8Array(data.length + n);
  res.set(data);
  for (let i = 0; i < data.length; i++) {
    const coef = res[i];
    if (coef !== 0) for (let j = 1; j < g.length; j++) res[i + j] ^= gmul(g[j], coef);
  }
  return Array.from(res.slice(data.length));
}

// [dataCodewords, eccPerBlock, numBlocks] for ECC level M
const SPECS = { 1: [16, 10, 1], 2: [28, 16, 1], 3: [44, 26, 1], 4: [64, 18, 2] };
const ALIGN = { 1: [], 2: [6, 18], 3: [6, 22], 4: [6, 26] };

function toBytes(str) {
  const out = [];
  for (const ch of unescape(encodeURIComponent(str))) out.push(ch.charCodeAt(0));
  return out;
}

function pickVersion(len) {
  for (const v of [1, 2, 3, 4]) {
    const [dataCw] = SPECS[v];
    if (4 + 8 + len * 8 <= dataCw * 8) return v;
  }
  throw new Error('Données trop longues pour ce générateur QR');
}

function buildCodewords(bytes, version) {
  const [dataCw, eccCw, blocks] = SPECS[version];
  const bits = [];
  const push = (val, n) => { for (let i = n - 1; i >= 0; i--) bits.push((val >> i) & 1); };
  push(4, 4);
  push(bytes.length, 8);
  for (const b of bytes) push(b, 8);
  const cap = dataCw * 8;
  for (let i = 0; i < 4 && bits.length < cap; i++) bits.push(0);
  while (bits.length % 8 !== 0) bits.push(0);
  const data = [];
  for (let i = 0; i < bits.length; i += 8) {
    let v = 0;
    for (let j = 0; j < 8; j++) v = (v << 1) | bits[i + j];
    data.push(v);
  }
  const pads = [0xec, 0x11];
  let k = 0;
  while (data.length < dataCw) data.push(pads[k++ % 2]);

  const perBlock = dataCw / blocks;
  const dataBlocks = [], eccBlocks = [];
  for (let b = 0; b < blocks; b++) {
    const chunk = data.slice(b * perBlock, (b + 1) * perBlock);
    dataBlocks.push(chunk);
    eccBlocks.push(rsEncode(chunk, eccCw));
  }
  const out = [];
  for (let i = 0; i < perBlock; i++) for (const blk of dataBlocks) out.push(blk[i]);
  for (let i = 0; i < eccCw; i++) for (const blk of eccBlocks) out.push(blk[i]);
  return out;
}

function makeMatrix(version) {
  const size = 17 + 4 * version;
  const m = Array.from({ length: size }, () => new Array(size).fill(null));
  const res = Array.from({ length: size }, () => new Array(size).fill(false));
  const setF = (r, c, v) => { m[r][c] = v; res[r][c] = true; };

  const finder = (r0, c0) => {
    for (let r = -1; r <= 7; r++) for (let c = -1; c <= 7; c++) {
      const r1 = r0 + r, c1 = c0 + c;
      if (r1 < 0 || r1 >= size || c1 < 0 || c1 >= size) continue;
      const inRing = (r >= 0 && r <= 6 && (c === 0 || c === 6)) || (c >= 0 && c <= 6 && (r === 0 || r === 6));
      const inCore = r >= 2 && r <= 4 && c >= 2 && c <= 4;
      setF(r1, c1, inRing || inCore);
    }
  };
  finder(0, 0); finder(0, size - 7); finder(size - 7, 0);

  for (let i = 8; i < size - 8; i++) { setF(6, i, i % 2 === 0); setF(i, 6, i % 2 === 0); }

  const centers = ALIGN[version];
  for (const r0 of centers) for (const c0 of centers) {
    if ((r0 === 6 && c0 === 6) || (r0 === 6 && c0 === size - 7) || (r0 === size - 7 && c0 === 6)) continue;
    for (let r = -2; r <= 2; r++) for (let c = -2; c <= 2; c++)
      setF(r0 + r, c0 + c, Math.max(Math.abs(r), Math.abs(c)) !== 1);
  }

  setF(size - 8, 8, true); // dark module
  for (let i = 0; i < 9; i++) { if (m[8][i] === null) setF(8, i, false); if (m[i][8] === null) setF(i, 8, false); }
  for (let i = 0; i < 8; i++) { if (m[8][size - 1 - i] === null) setF(8, size - 1 - i, false); if (m[size - 1 - i][8] === null) setF(size - 1 - i, 8, false); }
  return { m, res, size };
}

function placeData(m, res, size, cw) {
  const bits = [];
  for (const b of cw) for (let i = 7; i >= 0; i--) bits.push((b >> i) & 1);
  let idx = 0, up = true;
  for (let col = size - 1; col >= 1; col -= 2) {
    if (col === 6) col--;
    for (let n = 0; n < size; n++) {
      const row = up ? size - 1 - n : n;
      for (const c of [col, col - 1]) {
        if (!res[row][c]) { m[row][c] = idx < bits.length ? bits[idx++] === 1 : false; }
      }
    }
    up = !up;
  }
}

function maskFn(k, r, c) {
  switch (k) {
    case 0: return (r + c) % 2 === 0;
    case 1: return r % 2 === 0;
    case 2: return c % 3 === 0;
    case 3: return (r + c) % 3 === 0;
    case 4: return (Math.floor(r / 2) + Math.floor(c / 3)) % 2 === 0;
    case 5: return ((r * c) % 2) + ((r * c) % 3) === 0;
    case 6: return (((r * c) % 2) + ((r * c) % 3)) % 2 === 0;
    case 7: return (((r + c) % 2) + ((r * c) % 3)) % 2 === 0;
  }
}

function formatBits(mask) {
  const ecc = 0; // level M
  let data = (ecc << 3) | mask;
  let rem = data;
  for (let i = 0; i < 10; i++) rem = (rem << 1) ^ (((rem >> 9) & 1) * 0x537);
  return ((data << 10) | rem) ^ 0x5412;
}

function applyFormat(m, size, mask) {
  const bits = formatBits(mask);
  const get = (i) => ((bits >> i) & 1) === 1;
  for (let i = 0; i <= 5; i++) m[i][8] = get(i);
  m[7][8] = get(6); m[8][8] = get(7); m[8][7] = get(8);
  for (let i = 9; i <= 14; i++) m[8][14 - i] = get(i);
  for (let i = 0; i <= 7; i++) m[8][size - 1 - i] = get(i);
  for (let i = 8; i <= 14; i++) m[size - 15 + i][8] = get(i);
  m[size - 8][8] = true;
}

function penalty(m, size) {
  let p = 0;
  for (let r = 0; r < size; r++) {
    for (const line of [m[r], m.map((row) => row[r])]) {
      let run = 1;
      for (let i = 1; i < size; i++) {
        if (line[i] === line[i - 1]) { run++; } else { if (run >= 5) p += 3 + (run - 5); run = 1; }
      }
      if (run >= 5) p += 3 + (run - 5);
    }
  }
  for (let r = 0; r < size - 1; r++) for (let c = 0; c < size - 1; c++) {
    const v = m[r][c];
    if (v === m[r][c + 1] && v === m[r + 1][c] && v === m[r + 1][c + 1]) p += 3;
  }
  const pat = [true, false, true, true, true, false, true, false, false, false, false];
  const pat2 = [false, false, false, false, true, false, true, true, true, false, true];
  for (let r = 0; r < size; r++) for (let c = 0; c <= size - 11; c++) {
    let ok1 = true, ok2 = true, ok3 = true, ok4 = true;
    for (let i = 0; i < 11; i++) {
      if (m[r][c + i] !== pat[i]) ok1 = false;
      if (m[r][c + i] !== pat2[i]) ok2 = false;
      if (m[c + i][r] !== pat[i]) ok3 = false;
      if (m[c + i][r] !== pat2[i]) ok4 = false;
    }
    if (ok1) p += 40; if (ok2) p += 40; if (ok3) p += 40; if (ok4) p += 40;
  }
  let dark = 0;
  for (let r = 0; r < size; r++) for (let c = 0; c < size; c++) if (m[r][c]) dark++;
  const ratio = (dark * 100) / (size * size);
  p += Math.floor(Math.abs(ratio - 50) / 5) * 10;
  return p;
}

function qrMatrix(text) {
  const bytes = toBytes(text);
  const version = pickVersion(bytes.length);
  const cw = buildCodewords(bytes, version);
  let best = null, bestP = Infinity;
  for (let mask = 0; mask < 8; mask++) {
    const { m, res, size } = makeMatrix(version);
    placeData(m, res, size, cw);
    for (let r = 0; r < size; r++) for (let c = 0; c < size; c++) if (!res[r][c] && maskFn(mask, r, c)) m[r][c] = !m[r][c];
    applyFormat(m, size, mask);
    const p = penalty(m, size);
    if (p < bestP) { bestP = p; best = m; }
  }
  return best;
}

/* --------------------------------------------------------------- */

/* Palette APII : jaune de marque + gris anthracite */
/* Palette relevée sur le logo APII : jaune #FFCC00, gris #5F5F5F, rouge #FF0000 */
const C = {
  bg: '#F2F2F0', surface: '#FFFFFF', border: '#D9D9D6',
  ink: '#1F1F1E', soft: '#6E6E6C',
  accent: '#FFCC00', accentSoft: '#FFF3C7', accentInk: '#7A5F00',
  steel: '#454545', steelMid: '#5F5F5F', steelSoft: '#E9E9E7',
  green: '#35723F', greenSoft: '#E5EFE6',
  amber: '#A85B12', amberSoft: '#F8E8D9',
  red: '#C41A1A', redSoft: '#FAE0E0',
};

/* Le jaune de marque exige du texte foncé pour rester lisible. */
const onColor = (bg) => (bg === C.accent ? C.ink : '#fff');

/* Les commandes sont rattachées à une affaire : numéro + libellé du chantier. */
const AFFAIRES_INITIALES = [
  { numero: 'A-2601', libelle: 'Ambassade de Malaisie — Fresnes' },
  { numero: 'A-2602', libelle: 'La Grande Récré — Italie 2' },
  { numero: 'A-2603', libelle: 'ALDI Charenton' },
  { numero: 'A-2604', libelle: 'Jouars-Pontchartrain' },
  { numero: 'A-2605', libelle: 'Opération 804 — Melun' },
  { numero: 'A-2606', libelle: 'Groupe Scolaire Pasteur — Fresnes' },
];
/* Une unité sans date de révision connue est mise en quarantaine :
   mieux vaut la bloquer que la faire partir sur un chantier. */
/* Masques mutualisés (visiteur, VA Plomb) : même statut simplifié que le
   reste du parc, mais réforme fixée dès l'import pour les unités déjà
   réformées ou disparues (fusionnées) au moment du transfert du fichier. */
function masqueDepuisImport(p, famille) {
  const reforme = !!p.reforme;
  return {
    id: uid(), type: famille,
    name: p.n + (p.taille ? ` — Taille ${p.taille}` : ''),
    tag: p.t || '', etat: 'propre', comment: '',
    lieu: reforme ? 'Réformé' : 'Dépôt', dispo: !reforme,
    dateRevision: p.d || todayISO(),
    reforme, reformeComment: p.rc || '', reformeDate: p.rd || (reforme ? todayISO() : ''),
  };
}

function uniteDepuisParc(p) {
  const sansDate = !p.d;
  const bloque = !!p.hs || sansDate;
  return {
    id: uid(), type: p.y || 'Autre', name: p.n, tag: p.t || '', etat: p.hs ? 'hs' : 'propre',
    comment: p.c || '', lieu: bloque ? 'Quarantaine' : 'Dépôt', dispo: !bloque,
    dateRevision: p.d || '2000-01-01',
  };
}

/* ---------------------------------------------------------------
   Masques respiratoires mutualisés — importés du fichier de suivi EPI.
   n = désignation, t = n° interne, taille, d = date de mise en service,
   reforme/rc/rd = déjà réformé (ou disparu, fusionné) à l'import.
   --------------------------------------------------------------- */
const MASQUES_VISITEUR_INITIAL = [
  {n:'Masque VA', t:'104', taille:'M', d:'2026-02-25'},
  {n:'Masque VA', t:'61', taille:'L', d:'2025-02-11'},
  {n:'Masque VA', t:'106', taille:'M', d:'2026-02-25'},
  {n:'Masque VA', t:'109', taille:'L', d:'2025-10-15'},
  {n:'Masque VA', t:'103', taille:'L', d:'2025-10-31'},
  {n:'Masque VA', t:'91', taille:'S', d:'2026-06-18', reforme:1, rc:'Pièce faciale Mis au rebut le 18/06/2026', rd:'2026-06-18'},
  {n:'Masque VA', t:'101', taille:'L', d:'2026-06-26', reforme:1, rc:'Mis au rebut (BSDA 83ewk)', rd:'2026-06-26'},
  {n:'Masque VA', t:'102', taille:'L', d:'', reforme:1, rc:'Disparu — Non rendu Ancien masque 2026 DA CRUZ SILVA', rd:''},
  {n:'Masque VA', t:'111', taille:'M', d:'', reforme:1, rc:'Disparu — Non rendu Ancien masque 2026 SACKO', rd:''},
];

const VA_PLOMB_INITIAL = [
  {n:'Masque VA Plomb', t:'90', taille:'L', d:'', c:'Ancien masque PINTO DA LUZ David (2024) / visiteur 1'},
  {n:'Masque VA Plomb', t:'8', taille:'M', d:'', c:'Ancien masque MAIGA Mohamed (2023)'},
];

/* ---------------------------------------------------------------
   Masques respiratoires attribués nominativement — importés du fichier
   de suivi EPI. Un masque = une personne, en dehors du circuit des
   commandes de chantier. Renouvelé entièrement à échéance (365 j).
   --------------------------------------------------------------- */
const MASQUES_ATTRIBUES_INITIAL = [
  {nom:'APAEV Ramzan', type:'VA', interne:'110', masque:'230610050090034L', taille:'L', reception:'2025-10-09', service:'2025-10-09', fitTest:'2025-10-07'},
  {nom:'BAUDON Edouard', type:'VA', interne:'91', masque:'252510050090056S', taille:'S', reception:'2026-06-17', service:'2026-06-18', fitTest:'2026-04-27'},
  {nom:'CIUBOTARU Florin', type:'VA', interne:'2', masque:'260210050090003M', taille:'M', reception:'2026-04-14', service:'2026-05-13', fitTest:'2026-05-13'},
  {nom:'DIA Abdoulaye', type:'VA', interne:'73', masque:'252510050090057S', taille:'S', reception:'2026-05-15', service:'2026-05-15', fitTest:'2026-05-15'},
  {nom:'DIOMANDE Moussa', type:'VA', interne:'88', masque:'250210050090069M', taille:'M', reception:'2026-01-08', service:'2026-01-09', fitTest:'2025-12-09'},
  {nom:'KACHOUR Bekkaye', type:'VA', interne:'24', masque:'240310050090178M', taille:'M', reception:'2025-10-24', service:'2025-10-24', fitTest:'2025-10-24'},
  {nom:'KALLO Lancine', type:'VA', interne:'98', masque:'232210050090044M', taille:'M', reception:'2025-10-07', service:'2025-10-07', fitTest:'2025-10-07'},
  {nom:'MAIGA Mohamed', type:'VA', interne:'8', masque:'250210050090127M', taille:'M', reception:'2026-01-08', service:'2026-01-27', fitTest:'2026-01-27'},
  {nom:'MALENGE James', type:'VA', interne:'108', masque:'250210050090021M', taille:'M', reception:'2025-06-17', service:'2025-10-06', fitTest:'2025-10-06'},
  {nom:'SANGARE Moussa', type:'VA', interne:'101', masque:'250210050090184L', taille:'L', reception:'2026-07-03', service:'2026-07-03', fitTest:'2026-07-03'},
  {nom:'SANGARE NABI NOUHOUN Kader', type:'VA', interne:'105', masque:'250210050090019M', taille:'M', reception:'2026-03-05', service:'2026-03-06', fitTest:'2026-03-06'},
  {nom:'SISSOKO Mamadou', type:'VA', interne:'20', masque:'240310050090181M', taille:'M', reception:'2026-01-08', service:'2026-01-08', fitTest:'2026-01-08'},
  {nom:'SORO Pahafolo', type:'VA', interne:'9', masque:'250210050090179L', taille:'L', reception:'2025-09-08', service:'2025-09-09', fitTest:'2025-09-01'},
  {nom:'TIEHI Marius', type:'VA', interne:'113', masque:'260210050090004M', taille:'M', reception:'2026-04-14', service:'2026-04-15', fitTest:'2026-04-13'},
  {nom:'WAGUE Bokara', type:'VA', interne:'19', masque:'222110050090074L', taille:'L', reception:'2026-02-23', service:'2026-02-23', fitTest:'2026-02-23'},
  {nom:'APAEV Ramzan', type:'AA', interne:'110A', masque:'414231', taille:'L', reception:'2026-06-03', service:'2026-06-05', fitTest:'2026-06-05'},
  {nom:'CIUBOTARU Florin', type:'AA', interne:'02A', masque:'412575', taille:'M', reception:'2026-06-03', service:'2026-06-05', fitTest:'2026-06-05'},
  {nom:'KACHOUR Bekkaye', type:'AA', interne:'24A', masque:'412574', taille:'M', reception:'2026-06-03', service:'2026-06-05', fitTest:'2026-06-05'},
  {nom:'SISSOKO Mamadou', type:'AA', interne:'20A', masque:'412576', taille:'M', reception:'2026-06-03', service:'2026-06-05', fitTest:'2026-06-05'},
];

const libelleAffaire = (a) => (a ? `${a.numero} — ${a.libelle}` : '—');
const premiereLivraison = () => addDays(todayISO(), Math.ceil(DELAI_LIVRAISON_H / 24));

const UNITES = ['u', 'sacs', 'boîtes', 'rouleaux', 'paires', 'm', 'm²', 'm³', 'L', 'kg'];

const ROLES = {
  conducteur: { label: "Chargé d'affaires", desc: 'Crée les commandes, suit le parc', color: C.steelMid },
  magasinier: { label: 'Magasinier', desc: 'Prépare, scanne les départs et les replis', color: C.accent },
  chantier: { label: 'Chef de chantier', desc: "Passe les commandes d'appoint depuis le chantier", color: C.green },
  admin: { label: 'Administrateur', desc: 'Réservé au responsable — un seul compte', color: C.steel },
};

const ETATS = {
  propre: { label: 'Propre', color: C.green, soft: C.greenSoft, icon: CircleCheck },
  sale: { label: 'Sale', color: C.amber, soft: C.amberSoft, icon: Droplets },
  hs: { label: 'HS', color: C.red, soft: C.redSoft, icon: Ban },
};

const TYPES_CMD = {
  initiale: { label: 'Commande initiale', court: 'Initiale', color: C.steelMid, soft: C.steelSoft },
  appoint: { label: "Commande d'appoint", court: 'Appoint', color: C.green, soft: C.greenSoft },
};

const STATUTS = {
  a_preparer: { label: 'À préparer', color: C.steelMid, soft: C.steelSoft },
  chargee: { label: 'Sur chantier', color: C.accentInk, soft: C.accentSoft },
  repliee: { label: 'Repliée', color: C.green, soft: C.greenSoft },
};

/* ---------------------------------------------------------------
   Catalogue importé de Consommables.xlsx.
   CONSOMMABLES_INITIAUX : stock tenu, seuil d'alerte, QR par référence.
                           u = unité de mesure proposée, modifiable.
   OUTILLAGE_INITIAL     : outillage de chantier, ni stock ni révision.
   --------------------------------------------------------------- */
const CONSOMMABLES_INITIAUX = [
  {n:'Affiche attention plomb', u:'u'},
  {n:'Affiche chantier interdit au public', u:'u'},
  {n:'Affiche dange amiante', u:'u'},
  {n:'Affiche protection respiratoire obligatoire', u:'u'},
  {n:'Agrafe', u:'boîtes'},
  {n:'Anti rouille', u:'u'},
  {n:'Big bag amiante', u:'u'},
  {n:'Big bag plomb', u:'u'},
  {n:'Body benne', u:'u'},
  {n:'Boite de lingette', u:'boîtes'},
  {n:'Bombe de colle', u:'u'},
  {n:'Burin à pointe t300', u:'u'},
  {n:'Burin à pointe t500', u:'u'},
  {n:'Burin plat t300', u:'u'},
  {n:'Burin plat t500', u:'u'},
  {n:'Camion peinture', u:'u'},
  {n:'Cartouche kasco', u:'u'},
  {n:'Chauffage soufflante', u:'u'},
  {n:'Cheville a frapper', u:'boîtes'},
  {n:'Chiffon', u:'kg'},
  {n:'Combinaison', u:'u'},
  {n:'Corde confinement', u:'m'},
  {n:'Crochet confinement à corde', u:'u'},
  {n:'Depot bag 1,60m', u:'u'},
  {n:'Depot bag 2,10m', u:'u'},
  {n:'Depot bag 2,60m', u:'u'},
  {n:'Depot bag 3,10m', u:'u'},
  {n:'Disque a tronconner 125', u:'u'},
  {n:'Disque decoupage inox', u:'u'},
  {n:'Disque poncage 125', u:'u'},
  {n:'Disque poncage 180', u:'u'},
  {n:'Disque poncage 250', u:'u'},
  {n:'Eponge maçon', u:'u'},
  {n:'Film etirable transparent', u:'rouleaux'},
  {n:'Filtre ephemere 2500', u:'u'},
  {n:'Filtre ephemere b400/b10000', u:'u'},
  {n:'Filtre ephemere b50/b200', u:'u'},
  {n:'Filtre primaire 2500', u:'u'},
  {n:'Filtre primmaire b10000', u:'u'},
  {n:'Filtre primmaire b200', u:'u'},
  {n:'Filtre primmaire b400', u:'u'},
  {n:'Filtre primmaire b50', u:'u'},
  {n:'Filtre ucf 25micron', u:'u'},
  {n:'Filtre ucf 5micron', u:'u'},
  {n:'Gant de manutention', u:'paires'},
  {n:'Gant en latex', u:'paires'},
  {n:'Gel douche', u:'L'},
  {n:'Gel hydrique polyasim', u:'L'},
  {n:'Lames à grattoir', u:'u'},
  {n:'Lames scie sabre', u:'u'},
  {n:'Liner benne', u:'u'},
  {n:'Lino', u:'m²'},
  {n:'Liteau', u:'u'},
  {n:'Pack d\'eau', u:'u'},
  {n:'Palette', u:'u'},
  {n:'Panneau d affiche mesure d en poussierement', u:'u'},
  {n:'Panneau d affiche zone de dechet', u:'u'},
  {n:'Panneaux osb', u:'u'},
  {n:'Perche pour rouleaux peinture', u:'u'},
  {n:'Pinceaux', u:'u'},
  {n:'Pistolet silicone', u:'u'},
  {n:'Polyasim depol', u:'L'},
  {n:'Polyasim fiberflam', u:'L'},
  {n:'Polyasim grip floor', u:'L'},
  {n:'Polyasim y', u:'L'},
  {n:'Primaire', u:'L'},
  {n:'Primaire support bois', u:'L'},
  {n:'Riflard', u:'u'},
  {n:'Rouleau de polyane 200 micron', u:'rouleaux'},
  {n:'Rouleau de polyane 80 micron', u:'rouleaux'},
  {n:'Rouleau mousse', u:'u'},
  {n:'Rouleau raboteuse', u:'u'},
  {n:'Rubalise', u:'rouleaux'},
  {n:'Rubalise amiante', u:'rouleaux'},
  {n:'Sac a gravats amiante', u:'u'},
  {n:'Sac a gravats neutre', u:'u'},
  {n:'Sac a manche', u:'u'},
  {n:'Sac amiante', u:'u'},
  {n:'Sac longo-pak', u:'u'},
  {n:'Sac transparent', u:'u'},
  {n:'Scotch double face', u:'rouleaux'},
  {n:'Scotch gris', u:'rouleaux'},
  {n:'Scotch orange', u:'rouleaux'},
  {n:'Silicone-mastique', u:'u'},
  {n:'Smart trip rouge', u:'u'},
  {n:'Smart trip vert', u:'u'},
  {n:'Sopalin', u:'rouleaux'},
  {n:'Sous vetement', u:'u'},
  {n:'Sous vetement coton/hiver', u:'u'},
  {n:'Visières de protection', u:'u'},
  {n:'Vis', u:'boîtes'},
  {n:'Wd40', u:'u'},
  {n:'White spirit', u:'L'},
];

const OUTILLAGE_INITIAL = [
  'Barnum',
  'Attache echelle couvreur',
  'Barriere heras',
  'Brosse metallique',
  'Burineur t300',
  'Burineur t500',
  'Cable alimentation groupe electrogene',
  'Cable coffret electrique',
  'Casque anti bruit',
  'Chauffage',
  'Cloche d\'aspiration makita',
  'Compresseur 150l',
  'Coupe-boulon',
  'Disqueuse 125',
  'Disqueuse 230',
  'Echaffaudage',
  'Echelle 2 marches- bleue',
  'Echelle couvreur',
  'Echelle retractable bleue',
  'Elingue',
  'Entre d\'air compensatoire',
  'Entre d\'air de reglage',
  'PIR 7 marches',
  'PIR 3-4 marches',
  'Grattoir dalles',
  'Harnees',
  'Hublot',
  'Kit visiteur',
  'Maillet',
  'Malle de secours',
  'Malle de matériel bekkaye',
  'Malle de matériel dia',
  'Malle de matériel maïga',
  'Marteaux-burin',
  'Masque cub-air',
  'Masse',
  'Micro onde',
  'Miroir',
  'Multiprise',
  'Pelle de chantier',
  'Perceuse makita',
  'Perceuse makita a baterrie',
  'Pied de biche',
  'Pioche',
  'Porte bois à clef',
  'Poubelle noir',
  'Poulie corde',
  'Pulvérisateur',
  'Rallonge 220 v',
  'Rallonge 380 v',
  'Rectifieuse 125',
  'Rectifieuse 180',
  'Ruban a led 220v',
  'Scie sabre',
  'Scrap-air',
  'Sangle cliquet',
  'Spatule',
  'Table',
  'Test fumee',
  'Trousse de secours',
  'Tuyau d\'evacuation',
  'Tuyax 25m',
  'Tuyax 50m',
  'Ventuses',
  'Vestiaires',
];

/* ---------------------------------------------------------------
   Parc matériel importé de PR 06 Annexe 3 — Suivi matériel.
   y = famille (onglet du fichier), n = désignation, t = n° de série,
   d = dernière révision, hs = non conforme ou au rebut, c = commentaire.
   --------------------------------------------------------------- */
const TYPES_MATERIEL = [
  'Anémomètres',
  'Aspirateurs',
  'Brumisateurs',
  'Contrôleurs de dépression',
  'Cubair',
  'Déprimogènes',
  'Fit test',
  'Groupes électrogènes',
  'Masques visiteur',
  'Rectifieuses / Raboteuses',
  'UCF / UF',
  'VA Plomb',
];

/* Les masques n'ont pas de cycle de révision : passé 365 jours, le masque
   part directement en réforme (renouvellement complet), il n'y a rien à
   réviser sur la même unité. */
/* Seule la famille VA Plomb suit ce régime simplifié — les masques
   visiteur sont réintégrés au régime complet du matériel (propre/sale/HS,
   révision) à la demande explicite de l'utilisateur. */
const FAMILLES_MASQUE = new Set(['VA Plomb']);
/* Ni les masques visiteur ni VA Plomb n'ont d'étiquette à imprimer : ils
   sont gravés directement sur l'objet. */
const FAMILLES_SANS_QR = new Set(['Masques visiteur', 'VA Plomb']);

const PARC_INITIAL = [
  {y:'Aspirateurs', n:'Aspirateur RONDA 2000GT', t:'83720120-4224-840', d:'2024-11-21'},
  {y:'Aspirateurs', n:'Aspirateur RONDA 2000GT', t:'83720120-4524-843', d:'2024-12-02'},
  {y:'Aspirateurs', n:'Aspirateur RONDA 2000GT', t:'83720120-4524-844', d:'2024-12-02'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2024/02474', d:'2024-12-11', c:'Numéro de scellé 3046'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2024/02475', d:'2024-12-11', c:'Numéro de scellé 0969'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2024/02476', d:'2024-12-11', c:'Numéro de scellé 0781'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2024/02472', d:'2024-12-11', c:'Numéro de scellé 0940'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2024/02471', d:'2024-12-11', c:'Numéro de scellé 0968'},
  {y:'Aspirateurs', n:'Aspirateur RONDA 2000GT', t:'83720120-0825-849', d:'2025-03-24', hs:1, c:'Non conforme. Mis au rebut remplacé par l\'aspirateur 83720120-3925-863'},
  {y:'Aspirateurs', n:'Aspirateur RONDA 2000GT', t:'83720120-0825-850', d:'2025-03-24', c:'Mis au rebut et remplacé par l\'aspirateur 83720120-3925-861'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2023/01076', d:'2025-06-19', c:'Numéro de scellé 0775'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2023/01077', d:'2025-06-19', c:'Numéro de scellé 0774'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2023/01078', d:'2025-06-19', c:'Numéro de scellé 0773'},
  {y:'Aspirateurs', n:'Aspirateur RONDA 2000GT', t:'83720120-3925-867', d:'2025-10-07'},
  {y:'Aspirateurs', n:'Aspirateur RONDA 2000GT', t:'83720120-3925-868', d:'2025-10-07'},
  {y:'Aspirateurs', n:'Aspirateur RONDA 2800GT', t:'821628264725-618', d:'2025-12-05'},
  {y:'Aspirateurs', n:'Aspirateur RONDA 2000GT', t:'83720120-3925-861', d:'2026-04-21'},
  {y:'Aspirateurs', n:'Aspirateur RONDA 2000GT', t:'83720120-3925-863', d:'2025-12-17'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2025/03032', d:'2026-02-03', c:'Numéro de scellé 0481'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2025/03037', d:'2026-02-03', c:'Numéro de scellé 0482'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2025/03036', d:'2026-02-03', c:'Numéro de scellé 647353'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 200 H', t:'AST/2025/03034', d:'2026-02-03', c:'Numéro de scellé 0052'},
  {y:'Aspirateurs', n:'Aspirateur BEAR 201 H', t:'AST/2025/03035', d:'2026-02-03', c:'Numéro de scellé 647355'},
  {y:'Anémomètres', n:'THERMO-anémomètre KIMO LVB', t:'1P160941784', d:'2025-12-12'},
  {y:'Anémomètres', n:'THERMO-anémomètre KIMO LVB', t:'1P170146173', d:'2026-03-09'},
  {y:'Anémomètres', n:'THERMO-anémomètre KIMO LVB', t:'1P201288140', d:'2025-12-12'},
  {y:'Anémomètres', n:'THERMO-anémomètre KIMO LVB', t:'1P190472605', d:'2026-03-09'},
  {y:'Fit test', n:'Testeur d\'ajustement de masques respiratoires OHD Quantifit 1', t:'86106843', d:'2026-07-31'},
  {y:'Brumisateurs', n:'Brumisateur IDFI Brumisateur Roulant-MDF16067', t:'1403014', d:'2024-10-01'},
  {y:'Brumisateurs', n:'Brumisateur GENERAC-MDF Brumisateur Roulant', t:'1500340', d:'2025-02-14'},
  {y:'Brumisateurs', n:'Brumisateur IDFI Brumisateur Roulant-MDF16067', t:'1500341', d:'2024-02-08', hs:1, c:'Non conforme. Hors service'},
  {y:'Brumisateurs', n:'Brumisateur IDFI MINI DF', t:'1502478', d:'2025-10-24'},
  {y:'Brumisateurs', n:'Brumisateur IDFI GENERAC MINI DF', t:'1600975', d:'2024-12-13', hs:1, c:'Non conforme. Hors service-Moteur fonctionne mais pas de brumisation'},
  {y:'Brumisateurs', n:'Brumisateur BRUMI BRUMI DF MINI', t:'GGI0018208', d:'2025-10-24'},
  {y:'Brumisateurs', n:'Brumisateur BRUMI Mini Brumisateur 4L', t:'1357', d:'2024-11-27'},
  {y:'Brumisateurs', n:'Brumisateur BRUMI Mini Brumisateur 4L', t:'1358', d:'2025-12-10'},
  {y:'Brumisateurs', n:'Brumisateur EPICAP Mini Brumisateur EPICAP', t:'1068', d:'2024-12-13'},
  {y:'Brumisateurs', n:'Brumisateur FEMTO Mini Brumisateur FEMTO', t:'17679', d:'2024-12-13'},
  {y:'Brumisateurs', n:'Brumisateur Brumisateur à hélice-Spray Stream', t:'CE2206', d:'2025-11-25'},
  {y:'Contrôleurs de dépression', n:'Contrôleur de dépression BULKAIR BULKAIR PM', t:'BULKAIR 002757', d:'2026-03-26'},
  {y:'Contrôleurs de dépression', n:'Contrôleur de dépression BULKAIR BULKAIR PM', t:'BULKAIR 002566', d:'2026-03-06'},
  {y:'Contrôleurs de dépression', n:'Contrôleur de dépression KIMO alarmiante KIMO', t:'5F200110741', d:'2021-09-27', hs:1, c:'Au rebut. n° Certificat: 20230124- 21/01/2023'},
  {y:'Cubair', n:'Système d\'adduction d\'air CUBAIR CUBAIR 1', t:'/01122017095', d:'2026-05-22'},
  {y:'Cubair', n:'Système d\'adduction d\'air CUBAIR CUBAIR 1', t:'102019005', d:'2023-03-13'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 50', t:'DEPB50-02', d:'2022-04-11'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 50', t:'09/F50B012', d:'2022-12-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 50', t:'10F50B010', d:'2022-04-11'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'08/F200B023', d:'2025-12-01'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'08/F200B024', d:'2025-06-17'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'09/F200B038', d:'2025-12-01'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'10/F200B126 (Double)', d:'2026-03-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'12/F200B0123', d:'2026-03-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'13/F200B056 (Double)', d:'2025-12-12'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'13/F200B219 (Double)', d:'2025-06-16'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'13/F200B221 (Double)', d:'2025-11-25'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'16/F200B010', d:'2025-06-17'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'16/F200B011', d:'2022-12-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'16/F200B012', d:'2025-12-12'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'16/F200B013', d:'2025-11-25'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 200', t:'97/F200B045', d:'2024-01-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH(BEACON) NPU 4000', t:'B1680 (Double)', d:'2026-03-26'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'06/F400B006', d:'2024-12-23'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'07/F400B007', d:'2025-06-17'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'08/F400B023', d:'2026-03-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'08/F400B024', d:'2025-02-14'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'08/F400B025', d:'2025-10-23'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'08/F400B041', d:'2022-08-07'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'08/F400B042', d:'2025-12-03'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'08/F400B043', d:'2025-10-29'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'08/F400B044', d:'2026-03-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'08/F400B045', d:'2025-11-25'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400/D', t:'12/F400B0010 (Double)', d:'2026-03-26'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'12/F400B024', d:'2025-10-23'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'12/F400B025', d:'2025-11-28'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'16/F400B020', d:'2026-03-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'16F400B021', d:'2026-03-10'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'16/F400B022', d:'2026-03-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'16/F400B023', d:'2026-03-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'16/F400B102', d:'2026-03-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'16/F400B103', d:'2025-02-14'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'16/F400B104', d:'2024-12-23'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'16/F400B105', d:'2022-04-27'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'16/F400B106', d:'2025-06-17'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 400', t:'98/F400B014', d:'2022-04-27'},
  {y:'Déprimogènes', n:'DEPRIMOGENE EXTRAMIANTE(BEACON) NPU 4000 D', t:'B 4746 (Double)', d:'2026-03-26'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 500', t:'09/F500B013', d:'2022-12-01'},
  {y:'Déprimogènes', n:'DEPRIMOGENE BEST B 500', t:'09/F500B014', d:'2022-04-27'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH NPU 5000', t:'15616 (Double)', d:'2026-03-26'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH NPU 5000', t:'15617 (Double)', d:'2026-03-26'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH NPU 5000', t:'15653 (Double)', d:'2025-12-12'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH NPU 5000', t:'15655 (Double)', d:'2025-12-12'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH NPU 5000', t:'16880', d:'2025-12-10'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH NPU 5000', t:'16881', d:'2025-12-10'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH NPU 5000', t:'16884', d:'2025-12-10'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH NPU 5000', t:'16885', d:'2025-12-12'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH NPU 5000', t:'16970', d:'2025-12-10'},
  {y:'Déprimogènes', n:'DEPRIMOGENE LAPRO NPU 5000', t:'B14281', d:'2022-03-22'},
  {y:'Déprimogènes', n:'DEPRIMOGENE LAPRO NPU 5000', t:'B14294', d:'2023-02-02'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH NPU 5000', t:'B14295', d:'2023-10-26'},
  {y:'Déprimogènes', n:'DEPRIMOGENE LAPRO NPU 5000', t:'B14296', d:'2022-06-28'},
  {y:'Déprimogènes', n:'DEPRIMOGENE LAPRO NPU 5000', t:'B14299', d:'2022-03-04'},
  {y:'Déprimogènes', n:'DEPRIMOGENE LAPRO NPU 5000', t:'B14301', d:'2022-10-07'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH B 10000', t:'B 14543', d:'2022-06-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH B 10000', t:'B 14552', d:'2022-06-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH B 10000', t:'B 14555', d:'2022-06-09'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH PRODUCTS NPU 2500 ECO', t:'20093', d:'2025-10-23'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH PRODUCTS NPU 2500 ECO', t:'20094', d:'2025-10-23'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH PRODUCTS NPU 2500 ECO', t:'20095', d:'2025-10-23'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH PRODUCTS NPU 2500 ECO', t:'20120', d:'2025-10-23'},
  {y:'Déprimogènes', n:'DEPRIMOGENE SMH PRODUCTS NPU 2500 ECO', t:'20144', d:'2025-10-23'},
  {y:'Groupes électrogènes', n:'Groupe électrogène GELEC PANTHER-68/62 YC', t:'1409104', d:'', c:'Date de dernière révision absente du fichier source.'},
  {y:'Rectifieuses / Raboteuses', n:'Rectifieuse Blastrac BG 250', t:'11483(petite)', d:'2025-10-29'},
  {y:'Rectifieuses / Raboteuses', n:'Rectifieuse Blastrac BG 250', t:'2468-B(grande)', d:'2025-02-14'},
  {y:'Rectifieuses / Raboteuses', n:'Rectifieuse Blastrac BG 250', t:'2650-B(grande)', d:'2025-10-29'},
  {y:'Rectifieuses / Raboteuses', n:'Rectifieuse Blastrac BG 250', t:'4124-B(grande)', d:'2025-02-14'},
  {y:'Rectifieuses / Raboteuses', n:'Rectifieuse HTC GL270 HD', t:'G21708141', d:'2024-11-27'},
  {y:'Rectifieuses / Raboteuses', n:'Rectifieuse HTC GL450 HD', t:'G41712141', d:'2023-05-16'},
  {y:'Rectifieuses / Raboteuses', n:'Rectifieuse HTC GL40D', t:'G51707282', d:'2022-06-09'},
  {y:'Rectifieuses / Raboteuses', n:'RABOTEUSE SCHWAMBORM BEF 201', t:'6348', d:'2022-06-04'},
  {y:'Rectifieuses / Raboteuses', n:'Décolleuse BLASTRAC BS110', t:'27152B', d:'2026-01-14'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EXTRAMIANTE WMS 250', t:'B-10430', d:'2026-02-19'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EXTRAMIANTE WMS150', t:'B-5171', d:'2025-02-14'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EXTRAMIANTE WMS150', t:'B-5793', d:'2022-12-01', hs:1, c:'Non conforme. Hors service -pièce'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EXTRAMIANTE WMS150', t:'B-7100', d:'2026-02-17'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EXTRAMIANTE WMS150', t:'B-7544', d:'2024-12-13'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EXTRAMIANTE WMS150', t:'B-9446', d:'2026-03-18'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EXTRAMIANTE WMS150', t:'B-9509', d:'2026-02-19'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EXTRAMIANTE WMS 250', t:'B-12865', d:'2025-12-05'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EXTRAMIANTE WMS 250', t:'B-4718', d:'2026-02-17'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EXTRAMIANTE WMS150', t:'B-12458', d:'2022-03-22', hs:1, c:'Non conforme. Hors service -pièce'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EXTRAMIANTE WMS150', t:'B-12687', d:'2026-02-19'},
  {y:'UCF / UF', n:'UF (pompe à eau) EPICAP UF30L', t:'000382', d:'2025-02-14'},
  {y:'UCF / UF', n:'UF (pompe à eau) EPICAP UF30L', t:'000383', d:'2025-06-17'},
  {y:'UCF / UF', n:'UF (pompe à eau) LAPRO PWWS', t:'B-16889', d:'2024-12-13'},
  {y:'UCF / UF', n:'Ballon d\'eau chaude DECONTA D30L', t:'195', d:'2026-02-18'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EPICAP 150L CUMULUS', t:'A2D000136', d:'2026-02-18'},
  {y:'UCF / UF', n:'UCF (Unité de chauffe et filtration) EPICAP 0213UCF300', t:'A2D000134', d:'2026-02-18'},
  {y:'UCF / UF', n:'UF (pompe à eau) EPICAP', t:'/ 000091', d:'2025-07-09'},
  {y:'Groupes électrogènes', n:'Groupe électrogène DIESEL AQUITAINE ENERGIE SDG8500SE', t:'', d:'', hs:1, c:'Date de dernière révision absente du fichier source. Non conforme. Hors service Batterie à changer'},
  {y:'Groupes électrogènes', n:'Groupe électrogène BLACKSTONE SGB 8500 D-ES', t:'', d:'2025-09-23'},
];




/* Reprise des unités importées avant l'ajout des familles : on retrouve la
   famille par le n° de série, sinon par mot-clé dans la désignation. */
const FAMILLE_PAR_SERIE = (() => {
  const m = {};
  PARC_INITIAL.forEach((p) => { if (p.t) m[p.t.trim()] = p.y; });
  return m;
})();

const MOTS_FAMILLE = [
  ['deprimogene', 'Déprimogènes'],
  ['aspirateur', 'Aspirateurs'],
  ['brumisateur', 'Brumisateurs'],
  ['ucf', 'UCF / UF'],
  ['pompe à eau', 'UCF / UF'],
  ['ballon', 'UCF / UF'],
  ['anémomètre', 'Anémomètres'],
  ['anemometre', 'Anémomètres'],
  ['contrôleur de dépression', 'Contrôleurs de dépression'],
  ['adduction', 'Cubair'],
  ['cubair', 'Cubair'],
  ['électrogène', 'Groupes électrogènes'],
  ['electrogene', 'Groupes électrogènes'],
  ['rectifieuse', 'Rectifieuses / Raboteuses'],
  ['raboteuse', 'Rectifieuses / Raboteuses'],
  ['décolleuse', 'Rectifieuses / Raboteuses'],
  ['ajustement', 'Fit test'],
  ['fit test', 'Fit test'],
];

function familleDe(u) {
  const parSerie = FAMILLE_PAR_SERIE[(u.tag || '').trim()];
  if (parSerie) return parSerie;
  const n = (u.name || '').toLowerCase();
  const trouve = MOTS_FAMILLE.find(([mot]) => n.includes(mot));
  return trouve ? trouve[1] : 'Autre';
}

/* Reprise des références importées avant l'ajout des unités de mesure. */
const UNITE_PAR_NOM = (() => {
  const m = {};
  CONSOMMABLES_INITIAUX.forEach((c) => { m[c.n.toLowerCase()] = c.u; });
  return m;
})();

/* Ces trois articles figuraient par erreur dans les deux colonnes du fichier :
   ce sont des équipements. On les retire du stock s'ils y ont été créés. */
const RECLASSES_EN_OUTILLAGE = ['casque anti bruit', "cloche d'aspiration makita", 'coupe-boulon'];

function migrerUnites(refs) {
  return refs.map((r) => {
    if (r.unit && r.unit !== 'u') return r;
    const u = UNITE_PAR_NOM[(r.name || '').toLowerCase()];
    return u ? { ...r, unit: u } : r;
  });
}

function migrerFamilles(units) {
  return units.map((u) => (u.type ? u : { ...u, type: familleDe(u) }));
}

/* Reprise : la distinction réforme/rebut testée entre la 3.4 et la 3.6 est
   abandonnée. Tout ce qui portait l'un ou l'autre marqueur redevient un seul
   état "Réformé", sans perte de la date ni du commentaire d'origine. */
function migrerVersReformeUnique(units) {
  return units.map((u) => {
    if (u.rebut === undefined && u.enReforme === undefined) return u;
    const horsService = !!u.rebut || !!u.enReforme;
    const commentaire = u.rebut ? u.rebutComment : u.reformeComment;
    const date = u.rebut ? u.rebutDate : u.reformeDate;
    const { rebut, rebutComment, rebutDate, enReforme, ...reste } = u;
    return { ...reste, reforme: horsService, reformeComment: commentaire || '', reformeDate: date || todayISO() };
  });
}

/* Reprise : les versions 3.5/3.6 ont mis tout le parc importé en réforme
   automatiquement, sans qu'aucun humain n'ait rien décidé. Cette marque
   automatique est identifiable par son commentaire, toujours le même.
   On la retire pour laisser la date de révision de chaque unité décider
   normalement (disponible, bientôt à réviser, ou en quarantaine si dépassée),
   comme si elle sortait d'un import neuf. On ne touche jamais une unité dont
   le commentaire a été modifié depuis : c'est le signe qu'elle a été
   examinée pour de vrai. */
const MARQUEUR_REFORME_AUTO = 'Import initial — à vérifier avant remise en service.';
function corrigerReformeAutomatique(units) {
  const statutParTag = {};
  PARC_INITIAL.forEach((p) => { if (p.t) statutParTag[p.t.trim()] = !!p.hs; });
  return units.map((u) => {
    if (!u.reforme || u.reformeComment !== MARQUEUR_REFORME_AUTO) return u;
    const hs = u.tag ? !!statutParTag[u.tag.trim()] : false;
    return {
      ...u,
      reforme: false, reformeComment: '',
      etat: hs ? 'hs' : 'propre',
      dispo: !hs,
      lieu: hs ? 'Quarantaine' : 'Dépôt',
    };
  });
}

const VERSION_APP = '6.0 — 05/09/2026';

const REVISION_JOURS = 365;
const DELAI_LIVRAISON_H = 24;   // aucune livraison le jour même
const ALERTE_JOURS = 60;
const DAY = 86400000;

const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
const codeFor = (kind, id) => `APII:${kind}:${id}`;

/* QR effectivement imprimé : si un lien public est configuré, le code devient
   une vraie URL ouvrable par n'importe quel appareil photo, se terminant par
   le même identifiant interne (après #) pour que le scan à l'intérieur de
   l'application continue de fonctionner à l'identique. */
const codeQR = (kind, id, base) => (base ? `${base.replace(/\/+$/, '')}#${codeFor(kind, id)}` : codeFor(kind, id));
const todayISO = () => new Date().toISOString().slice(0, 10);
const addDays = (iso, n) => new Date(new Date(iso + 'T12:00:00').getTime() + n * DAY).toISOString().slice(0, 10);
const daysUntil = (iso) => Math.round((new Date(iso + 'T12:00:00').getTime() - Date.now()) / DAY);
const frDate = (iso) => (iso ? new Date(iso + 'T12:00:00').toLocaleDateString('fr-FR') : '—');
function frDateHeure(iso) {
  if (!iso) return '—';
  const d = new Date(iso);
  return `${d.toLocaleDateString('fr-FR')} à ${d.toLocaleTimeString('fr-FR', { hour: '2-digit', minute: '2-digit' })}`;
}

function relTime(iso) {
  const diff = (Date.now() - new Date(iso).getTime()) / 1000;
  if (diff < 60) return "à l'instant";
  if (diff < 3600) return `il y a ${Math.floor(diff / 60)} min`;
  if (diff < 86400) return `il y a ${Math.floor(diff / 3600)} h`;
  const d = Math.floor(diff / 86400);
  return d === 1 ? 'hier' : d < 7 ? `il y a ${d} j` : new Date(iso).toLocaleDateString('fr-FR', { day: 'numeric', month: 'short' });
}

/* ---- état dérivé d'une unité de matériel ---- */
function prochaineRevision(u) {
  return addDays(u.dateRevision || todayISO(), REVISION_JOURS);
}
function etatUnite(u) {
  const next = prochaineRevision(u);
  const j = daysUntil(next);
  const masque = FAMILLES_MASQUE.has(u.type);
  if (u.reforme) return { key: 'reforme', label: masque ? 'Réformé' : 'Réformé — hors service', color: C.steel, soft: C.steelSoft, next, j };
  if (masque && j < 0 && u.dispo) return { key: 'reforme', label: 'Réformé — 365 jours atteints, à renouveler', color: C.steel, soft: C.steelSoft, next, j };
  if (u.etat === 'hs') return { key: 'hs', label: 'HS — quarantaine', color: C.red, soft: C.redSoft, next, j };
  if (j < 0 && u.dispo) return { key: 'perime', label: 'Révision dépassée — quarantaine', color: C.red, soft: C.redSoft, next, j };
  if (!u.dispo) return { key: 'chantier', label: 'Sur chantier', color: C.accentInk, soft: C.accentSoft, next, j };
  if (j <= ALERTE_JOURS) return { key: 'bientot', label: `Révision dans ${j} j`, color: C.amber, soft: C.amberSoft, next, j };
  return { key: 'dispo', label: 'Disponible', color: C.green, soft: C.greenSoft, next, j };
}
const estCommandable = (u) => {
  const e = etatUnite(u);
  return e.key === 'dispo' || e.key === 'bientot';
};


/* Logo APII détouré (couleurs de charte inchangées), embarqué dans l'application */
const LOGO = 'data:image/png;base64,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';
const LOGO_RATIO = 505 / 254;

/* Posé sur une pastille blanche : le gris et le rouge du logo ne sont pas lisibles
   directement sur un fond sombre. */
function Logo({ height = 30, plaque = true }) {
  const img = (
    <img src={LOGO} alt="APII — Désamiantage"
      style={{ height, width: height * LOGO_RATIO, objectFit: 'contain', display: 'block' }} />
  );
  if (!plaque) return img;
  return (
    <div className="rounded flex items-center justify-center flex-shrink-0"
      style={{ background: '#fff', padding: '4px 6px' }}>
      {img}
    </div>
  );
}

/* ---------------------------------------------------------------
   Générateur PDF minimal (texte Helvetica std 14 + rectangles), sans
   dépendance externe — pour les bons de livraison/repli.
   --------------------------------------------------------------- */
// Générateur PDF minimal, sans dépendance : texte (Helvetica std 14, WinAnsi),
// rectangles pleins (pour les QR), plusieurs pages. Écrit les octets à la main.

const PAGE_W = 595.28, PAGE_H = 841.89; // A4 en points (72 dpi)

// Table de correspondance Unicode -> octet WinAnsi (cp1252), pour les seuls
// caractères français utilisés dans l'application. Tout ce qui est <128 passe tel quel.
const WINANSI = {
  '\u20AC': 0x80, '\u2018': 0x91, '\u2019': 0x92, '\u201C': 0x93, '\u201D': 0x94,
  '\u2013': 0x96, '\u2014': 0x97, '\u00AB': 0xAB, '\u00BB': 0xBB, '\u00B7': 0xB7,
  '\u2026': 0x85, '\u2022': 0x95, '\u00A0': 0xA0, '\u00B2': 0xB2, '\u00B3': 0xB3,
  '\u2212': 0x2D, // signe moins typographique -> tiret simple (non prévu en WinAnsi)
  '\u2190': 0x3C, // flèche gauche -> '<' (dégradation ; non prévu en WinAnsi)
  '\u00C0': 0xC0, '\u00C7': 0xC7, '\u00C8': 0xC8, '\u00C9': 0xC9, '\u00CA': 0xCA,
  '\u00CE': 0xCE, '\u00D4': 0xD4, '\u00D9': 0xD9, '\u00DB': 0xDB,
  '\u00E0': 0xE0, '\u00E2': 0xE2, '\u00E7': 0xE7, '\u00E8': 0xE8, '\u00E9': 0xE9,
  '\u00EA': 0xEA, '\u00EB': 0xEB, '\u00EE': 0xEE, '\u00EF': 0xEF, '\u00F4': 0xF4,
  '\u00F6': 0xF6, '\u00F9': 0xF9, '\u00FB': 0xFB, '\u00FC': 0xFC,
  '\u0153': 0x9C, '\u0152': 0x8C, '\u00B0': 0xB0,
};

function pdfString(str) {
  let out = '(';
  for (const ch of String(str)) {
    const cp = ch.codePointAt(0);
    let byte;
    if (cp < 128) byte = cp;
    else if (WINANSI[ch] !== undefined) byte = WINANSI[ch];
    else byte = 0x3F; // '?' de repli pour un caractère non prévu
    if (byte === 0x28 || byte === 0x29 || byte === 0x5C) out += '\\' + String.fromCharCode(byte);
    else if (byte < 32 || byte > 126) out += '\\' + byte.toString(8).padStart(3, '0');
    else out += String.fromCharCode(byte);
  }
  return out + ')';
}

// Largeurs Helvetica / Helvetica-Bold (unités = 1/1000 em), table AFM standard,
// utilisée pour retourner la ligne à la largeur disponible.
const HELV_W = {32:278,33:278,34:355,35:556,36:556,37:889,38:667,39:191,40:333,41:333,42:389,43:584,44:278,45:333,46:278,47:278,48:556,49:556,50:556,51:556,52:556,53:556,54:556,55:556,56:556,57:556,58:278,59:278,60:584,61:584,62:584,63:556,64:1015,65:667,66:667,67:722,68:722,69:667,70:611,71:778,72:722,73:278,74:500,75:667,76:556,77:833,78:722,79:778,80:667,81:778,82:722,83:667,84:611,85:722,86:667,87:944,88:667,89:667,90:611,91:278,92:278,93:278,94:469,95:556,96:333,97:556,98:556,99:500,100:556,101:556,102:278,103:556,104:556,105:222,106:222,107:500,108:222,109:833,110:556,111:556,112:556,113:556,114:333,115:500,116:278,117:556,118:500,119:722,120:500,121:500,122:500,123:334,124:260,125:334,126:584,128:556,138:556,140:1000,142:611,145:222,146:222,147:333,148:333,150:556,151:1000,154:500,156:722,158:500,159:667,160:278,161:333,162:556,163:556,164:556,165:556,166:260,167:556,168:333,169:737,170:370,171:556,172:584,173:333,174:737,175:333,176:400,177:584,178:333,179:333,180:333,181:556,182:537,183:278,184:333,185:333,186:365,187:556,188:834,189:834,190:834,191:611,192:667,193:667,194:667,195:667,196:667,197:667,198:1000,199:722,200:667,201:667,202:667,203:667,204:278,205:278,206:278,207:278,208:722,209:722,210:778,211:778,212:778,213:778,214:778,215:584,216:778,217:722,218:722,219:722,220:722,221:667,222:667,223:611,224:556,225:556,226:556,227:556,228:556,229:556,230:889,231:500,232:556,233:556,234:556,235:556,236:278,237:278,238:278,239:278,240:556,241:556,242:556,243:556,244:556,245:556,246:556,247:584,248:611,249:556,250:556,251:556,252:556,253:500,254:556,255:500};
const HELVB_W = {32:278,33:333,34:474,35:556,36:556,37:889,38:722,39:238,40:333,41:333,42:389,43:584,44:278,45:333,46:278,47:278,48:556,49:556,50:556,51:556,52:556,53:556,54:556,55:556,56:556,57:556,58:333,59:333,60:584,61:584,62:584,63:611,64:975,65:722,66:722,67:722,68:722,69:667,70:611,71:778,72:722,73:278,74:556,75:722,76:611,77:833,78:722,79:778,80:667,81:778,82:722,83:667,84:611,85:722,86:667,87:944,88:667,89:667,90:611,91:333,92:278,93:333,94:584,95:556,96:333,97:556,98:611,99:556,100:611,101:556,102:333,103:611,104:611,105:278,106:278,107:556,108:278,109:889,110:611,111:611,112:611,113:611,114:389,115:556,116:333,117:611,118:556,119:778,120:556,121:556,122:500,123:389,124:280,125:389,126:584,128:556,138:556,140:1000,142:611,145:278,146:278,147:500,148:500,150:556,151:1000,154:556,156:722,158:556,159:667,160:278,161:333,162:556,163:556,164:556,165:556,166:280,167:556,168:333,169:737,170:370,171:556,172:584,173:333,174:737,175:333,176:400,177:584,178:333,179:333,180:333,181:611,182:556,183:278,184:333,185:333,186:365,187:556,188:834,189:834,190:834,191:611,192:722,193:722,194:722,195:722,196:722,197:722,198:1000,199:722,200:667,201:667,202:667,203:667,204:278,205:278,206:278,207:278,208:722,209:722,210:778,211:778,212:778,213:778,214:778,215:584,216:778,217:722,218:722,219:722,220:722,221:667,222:667,223:611,224:556,225:556,226:556,227:556,228:556,229:556,230:889,231:556,232:556,233:556,234:556,235:556,236:278,237:278,238:278,239:278,240:611,241:611,242:611,243:611,244:611,245:611,246:611,247:584,248:611,249:611,250:611,251:611,252:611,253:556,254:611,255:556};

function largeurTexte(str, size, gras) {
  const table = gras ? HELVB_W : HELV_W;
  let w = 0;
  for (const ch of String(str)) {
    const cp = ch.codePointAt(0);
    const byte = cp < 128 ? cp : (WINANSI[ch] !== undefined ? WINANSI[ch] : 0x3F);
    w += (table[byte] || 556);
  }
  return (w / 1000) * size;
}

// Coupe un texte en lignes tenant dans maxWidth (retour à la ligne simple, mot par mot).
function retourALaLigne(str, size, gras, maxWidth) {
  const mots = String(str).split(' ');
  const lignes = [];
  let courante = '';
  for (const mot of mots) {
    const essai = courante ? courante + ' ' + mot : mot;
    if (largeurTexte(essai, size, gras) > maxWidth && courante) {
      lignes.push(courante);
      courante = mot;
    } else {
      courante = essai;
    }
  }
  if (courante) lignes.push(courante);
  return lignes;
}

class PdfDoc {
  constructor() {
    this.pages = [];
    this.page = null;
  }
  addPage() {
    this.page = { ops: [] };
    this.pages.push(this.page);
    return this.page;
  }
  // y donné depuis le HAUT de la page (comme une mise en page habituelle) ;
  // converti en repère PDF (origine en bas) au moment d'écrire l'opérateur.
  texte(x, yHaut, str, { size = 10, gras = false, couleur = [0, 0, 0] } = {}) {
    const y = PAGE_H - yHaut;
    const font = gras ? '/F2' : '/F1';
    const [r, g, b] = couleur;
    this.page.ops.push(
      `q ${r} ${g} ${b} rg BT ${font} ${size} Tf ${x.toFixed(2)} ${y.toFixed(2)} Td ${pdfString(str)} Tj ET Q`
    );
  }
  rectPlein(x, yHaut, w, h, couleur = [0, 0, 0]) {
    const y = PAGE_H - yHaut - h;
    const [r, g, b] = couleur;
    this.page.ops.push(`q ${r} ${g} ${b} rg ${x.toFixed(2)} ${y.toFixed(2)} ${w.toFixed(2)} ${h.toFixed(2)} re f Q`);
  }
  ligneH(x1, yHaut, x2, epaisseur = 0.4, couleur = [0.8, 0.8, 0.78]) {
    const y = PAGE_H - yHaut;
    const [r, g, b] = couleur;
    this.page.ops.push(`q ${r} ${g} ${b} RG ${epaisseur} w ${x1.toFixed(2)} ${y.toFixed(2)} m ${x2.toFixed(2)} ${y.toFixed(2)} l S Q`);
  }
  // Dessine une matrice de QR (tableau de tableaux de booléens) dans un carré
  // de côté `taille` pt, coin haut-gauche à (x, yHaut). Fusionne les modules
  // adjacents d'une même ligne en un seul rectangle, comme pour le SVG.
  qr(matrix, x, yHaut, taille) {
    if (!matrix) return;
    const n = matrix.length;
    const quiet = 4; // marge silencieuse à l'intérieur du carré, indispensable au scan
    const cell = taille / (n + quiet * 2);
    const ox = x + quiet * cell, oy = yHaut + quiet * cell;
    for (let r = 0; r < n; r++) {
      let c = 0;
      while (c < n) {
        if (!matrix[r][c]) { c++; continue; }
        let w = 1;
        while (c + w < n && matrix[r][c + w]) w++;
        this.rectPlein(ox + c * cell, oy + r * cell, w * cell, cell);
        c += w;
      }
    }
  }

  bytes() {
    const objs = [];
    const push = (content) => { objs.push(content); return objs.length; };

    const nPages = this.pages.length;
    const pageObjNums = [];
    const contentObjNums = [];

    // Réserve les numéros : 1 Catalog, 2 Pages, 3 Font Helv, 4 Font HelvB,
    // puis pour chaque page : un objet Page et un objet Content.
    const catalogNum = 1, pagesNum = 2, fontNum = 3, fontBNum = 4;
    let next = 5;
    for (let i = 0; i < nPages; i++) { pageObjNums.push(next++); contentObjNums.push(next++); }

    objs[catalogNum - 1] = `<< /Type /Catalog /Pages ${pagesNum} 0 R >>`;
    objs[pagesNum - 1] = `<< /Type /Pages /Count ${nPages} /Kids [${pageObjNums.map((n) => n + ' 0 R').join(' ')}] >>`;
    objs[fontNum - 1] = `<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>`;
    objs[fontBNum - 1] = `<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Bold /Encoding /WinAnsiEncoding >>`;

    this.pages.forEach((p, i) => {
      const stream = p.ops.join('\n');
      objs[pageObjNums[i] - 1] =
        `<< /Type /Page /Parent ${pagesNum} 0 R /MediaBox [0 0 ${PAGE_W} ${PAGE_H}] ` +
        `/Resources << /Font << /F1 ${fontNum} 0 R /F2 ${fontBNum} 0 R >> >> /Contents ${contentObjNums[i]} 0 R >>`;
      objs[contentObjNums[i] - 1] = { stream };
    });

    // Sérialisation avec suivi des offsets pour la table xref.
    let out = '%PDF-1.4\n%\xE2\xE3\xCF\xD3\n';
    const offsets = [0];
    for (let i = 0; i < objs.length; i++) {
      offsets.push(out.length);
      const o = objs[i];
      if (o && typeof o === 'object' && 'stream' in o) {
        const body = o.stream;
        out += `${i + 1} 0 obj\n<< /Length ${body.length} >>\nstream\n${body}\nendstream\nendobj\n`;
      } else {
        out += `${i + 1} 0 obj\n${o}\nendobj\n`;
      }
    }
    const xrefStart = out.length;
    out += `xref\n0 ${objs.length + 1}\n`;
    out += '0000000000 65535 f \n';
    for (let i = 1; i <= objs.length; i++) out += String(offsets[i]).padStart(10, '0') + ' 00000 n \n';
    out += `trailer\n<< /Size ${objs.length + 1} /Root ${catalogNum} 0 R >>\nstartxref\n${xrefStart}\n%%EOF`;
    return out;
  }
}



/* ---------------- QR ---------------- */

/* Un QR dessiné en un seul chemin SVG plutôt qu'en centaines de rectangles :
   sans ça, une planche d'étiquettes fige l'application. Les matrices sont
   mises en cache, leur calcul (8 masques testés) étant coûteux. */
const CACHE_QR = new Map();

function matriceQR(text) {
  if (CACHE_QR.has(text)) return CACHE_QR.get(text);
  let m = null;
  try { m = qrMatrix(text); } catch (e) { m = null; }
  if (CACHE_QR.size > 400) CACHE_QR.clear();
  CACHE_QR.set(text, m);
  return m;
}

function cheminQR(matrix) {
  const n = matrix.length;
  const d = [];
  for (let r = 0; r < n; r++) {
    let c = 0;
    while (c < n) {
      if (!matrix[r][c]) { c++; continue; }
      let w = 1;
      while (c + w < n && matrix[r][c + w]) w++;
      d.push(`M${c} ${r}h${w}v1h-${w}z`);
      c += w;
    }
  }
  return d.join('');
}

function QrSvg({ text, size = 120 }) {
  const data = useMemo(() => {
    const m = matriceQR(text);
    return m ? { d: cheminQR(m), n: m.length } : null;
  }, [text]);
  if (!data) return <div style={{ width: size, height: size, background: C.border }} />;
  const quiet = 2, total = data.n + quiet * 2;
  return (
    <svg width={size} height={size} viewBox={`0 0 ${total} ${total}`} shapeRendering="crispEdges">
      <rect width={total} height={total} fill="#fff" />
      <g transform={`translate(${quiet} ${quiet})`}><path d={data.d} fill="#000" /></g>
    </svg>
  );
}

/* ---------------- scanner ---------------- */

function CameraScanner({ onCode }) {
  const videoRef = useRef(null);
  const [status, setStatus] = useState('init');
  const lastRef = useRef({ code: null, at: 0 });

  useEffect(() => {
    let stream, raf, detector, cancelled = false;
    async function start() {
      if (typeof window === 'undefined' || !('BarcodeDetector' in window) || !navigator.mediaDevices) { setStatus('unsupported'); return; }
      try {
        detector = new window.BarcodeDetector({ formats: ['qr_code'] });
        stream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: { ideal: 'environment' } } });
        if (cancelled) { stream.getTracks().forEach((t) => t.stop()); return; }
        if (videoRef.current) { videoRef.current.srcObject = stream; await videoRef.current.play(); }
        setStatus('running');
        const tick = async () => {
          if (cancelled) return;
          try {
            if (videoRef.current && videoRef.current.readyState === 4) {
              const codes = await detector.detect(videoRef.current);
              if (codes.length) {
                const val = codes[0].rawValue, now = Date.now();
                if (val !== lastRef.current.code || now - lastRef.current.at > 2500) {
                  lastRef.current = { code: val, at: now };
                  onCode(val);
                }
              }
            }
          } catch (e) { /* frame ignorée */ }
          raf = requestAnimationFrame(tick);
        };
        raf = requestAnimationFrame(tick);
      } catch (e) { setStatus('denied'); }
    }
    start();
    return () => { cancelled = true; if (raf) cancelAnimationFrame(raf); if (stream) stream.getTracks().forEach((t) => t.stop()); };
  }, [onCode]);

  if (status === 'unsupported' || status === 'denied') {
    return (
      <div className="rounded-lg px-4 py-3 text-xs" style={{ background: C.amberSoft, color: C.amber }}>
        {status === 'denied'
          ? "Accès caméra refusé. Autorisez la caméra, ou touchez l'article dans la liste pour le valider."
          : "Ce navigateur ne lit pas les QR par caméra. Utilisez la saisie du code, ou touchez l'article dans la liste."}
      </div>
    );
  }
  return (
    <div className="relative rounded-lg overflow-hidden" style={{ background: '#000', aspectRatio: '4 / 3' }}>
      <video ref={videoRef} playsInline muted className="w-full h-full object-cover" />
      <div className="absolute inset-0 pointer-events-none flex items-center justify-center" aria-hidden="true">
        <div style={{ width: '58%', aspectRatio: '1', border: `3px solid ${C.accent}`, borderRadius: 12 }} />
      </div>
      {status === 'init' && (
        <div className="absolute inset-0 flex items-center justify-center"><Loader2 className="animate-spin" size={22} color="#fff" /></div>
      )}
    </div>
  );
}

/* =================== APPLICATION =================== */

export default function StockAPII() {
  const [users, setUsers] = useState([]);
  const [units, setUnits] = useState([]);
  const [refs, setRefs] = useState([]);
  const [commandes, setCommandes] = useState([]);
  const [journal, setJournal] = useState([]);
  const [alertEmails, setAlertEmails] = useState([]);
  const [urlPublique, setUrlPublique] = useState('');
  const [affaires, setAffaires] = useState([]);
  const [outils, setOutils] = useState([]);
  const [loading, setLoading] = useState(true);
  const [saveError, setSaveError] = useState(false);
  const [stockageOk, setStockageOk] = useState(true);
  const [masquesAttribues, setMasquesAttribues] = useState([]);

  const [me, setMe] = useState(null);
  const [tab, setTab] = useState('commandes');
  const [openCommande, setOpenCommande] = useState(null);
  const [scanMode, setScanMode] = useState(null);
  const [openUnit, setOpenUnit] = useState(null);
  const [openRef, setOpenRef] = useState(null);
  const [modal, setModal] = useState(null);
  const [notifier, setNotifier] = useState(null);
  const [affaireFilter, setAffaireFilter] = useState('toutes');
  const [formCmd, setFormCmd] = useState(null);   // 'initiale' | 'appoint' : saisie plein écran
  const [search, setSearch] = useState('');
  const [parcFilter, setParcFilter] = useState('tous');
  const [typeFilter, setTypeFilter] = useState('tous');
  const [consoVue, setConsoVue] = useState('conso');
  const [qrVue, setQrVue] = useState('materiel');
  const [qrSearch, setQrSearch] = useState('');
  const [qrPage, setQrPage] = useState(0);

  useEffect(() => {
    (async () => {
      /* La lecture lève une erreur tant que la clé n'existe pas : on l'isole
         pour que l'initialisation se fasse quand même sur une base vierge. */
      let d = {};
      try {
        const res = await window.storage.get('apii-stock-v3', true);
        if (res && res.value) d = JSON.parse(res.value);
      } catch (e) { /* première utilisation */ }

      setUsers(d.users || []);

      /* Catalogues chargés depuis les fichiers au premier lancement seulement. */
      const unitsCharges = d.units && d.units.length
        ? corrigerReformeAutomatique(migrerVersReformeUnique(migrerFamilles(d.units)))
        : [
            ...PARC_INITIAL.map(uniteDepuisParc),
            ...MASQUES_VISITEUR_INITIAL.map((p) => masqueDepuisImport(p, 'Masques visiteur')),
            ...VA_PLOMB_INITIAL.map((p) => masqueDepuisImport(p, 'VA Plomb')),
          ];
      const refsCharges = d.refs && d.refs.length
        ? migrerUnites(d.refs).filter((r) => !RECLASSES_EN_OUTILLAGE.includes((r.name || '').toLowerCase()))
        : CONSOMMABLES_INITIAUX.map((c) => ({ id: uid(), name: c.n, unit: c.u, quantity: 0, seuil: 10 }));
      const outilsCharges = d.outils && d.outils.length
        ? d.outils
        : OUTILLAGE_INITIAL.map((n) => ({ id: uid(), name: n }));
      const masquesCharges = d.masquesAttribues && d.masquesAttribues.length
        ? d.masquesAttribues
        : MASQUES_ATTRIBUES_INITIAL.map((m) => ({
            id: uid(), personne: m.nom, type: m.type, numeroInterne: m.interne, numeroMasque: m.masque,
            taille: m.taille, dateMiseEnService: m.service, dateFitTest: m.fitTest || '', reforme: false,
          }));

      setUnits(unitsCharges);
      setRefs(refsCharges);
      setOutils(outilsCharges);
      setMasquesAttribues(masquesCharges);

      /* Les reprises ci-dessus sont enregistrées une fois, pour ne pas se rejouer.
         Comparaison directe avant/après plutôt que de retester chaque règle ici. */
      const reprise =
        (d.units && JSON.stringify(d.units) !== JSON.stringify(unitsCharges)) ||
        (d.refs && JSON.stringify(d.refs) !== JSON.stringify(refsCharges));
      if (reprise) {
        try {
          await window.storage.set('apii-stock-v3',
            JSON.stringify({ ...d, units: unitsCharges, refs: refsCharges, outils: outilsCharges, masquesAttribues: masquesCharges }), true);
        } catch (e) { /* la reprise se refera au prochain chargement */ }
      }

      /* Sonde : l'enregistrement partagé n'existe que sur l'artifact publié.
         Sans elle, un compte créé dans l'aperçu semble fonctionner puis disparaît. */
      try {
        const ok = await window.storage.set('apii-sonde', String(Date.now()), true);
        setStockageOk(!!ok);
      } catch (e) { setStockageOk(false); }

      setCommandes(d.commandes || []); setJournal(d.journal || []);
      setAlertEmails(d.alertEmails || []);
      setUrlPublique(d.urlPublique || '');
      setAffaires(d.affaires && d.affaires.length
        ? d.affaires
        : AFFAIRES_INITIALES.map((a) => ({ id: uid(), ...a, ouverte: true })));

      try {
        const sess = await window.storage.get('apii-session', false);
        if (sess && sess.value) {
          const u = (d.users || []).find((x) => x.id === JSON.parse(sess.value).userId);
          if (u) setMe(u);
        }
      } catch (e) { /* pas de session enregistrée */ }

      setLoading(false);
    })();
  }, []);

  async function persist(next) {
    const state = { users, units, refs, outils, commandes, journal, alertEmails, affaires, urlPublique, masquesAttribues, ...next };
    setUsers(state.users); setUnits(state.units); setRefs(state.refs); setOutils(state.outils);
    setCommandes(state.commandes); setJournal(state.journal);
    setAlertEmails(state.alertEmails); setAffaires(state.affaires); setUrlPublique(state.urlPublique);
    setMasquesAttribues(state.masquesAttribues);
    try {
      const ok = await window.storage.set('apii-stock-v3', JSON.stringify(state), true);
      setSaveError(!ok);
      return !!ok;
    } catch (e) { setSaveError(true); return false; }
  }

  const log = (entry, base) => [{ id: uid(), date: new Date().toISOString(), par: me ? me.name : '—', ...entry }, ...(base || journal)];

  /* ---------- connexion ---------- */

  async function signIn(user) {
    setMe(user);
    try { await window.storage.set('apii-session', JSON.stringify({ userId: user.id }), false); } catch (e) { /* session non mémorisée */ }
  }
  async function signOut() {
    setMe(null); setTab('commandes'); setOpenCommande(null); setScanMode(null);
    try { await window.storage.delete('apii-session', false); } catch (e) { /* rien à supprimer */ }
  }
  async function createUser(d) {
    const u = { id: uid(), name: d.name, role: d.role, pin: d.pin, email: d.email || '', createdAt: new Date().toISOString() };
    const nextUsers = [...users, u];
    const ok = await persist({ users: nextUsers, journal: [{ id: uid(), date: new Date().toISOString(), par: d.name, type: 'compte', label: d.name, detail: `Compte créé — ${ROLES[d.role].label}` }, ...journal] });
    if (!ok) { setStockageOk(false); return; }
    signIn(u);
  }

  /* Création d'un compte équipe par l'administrateur, depuis "Mon profil" :
     contrairement à createUser (page de connexion), on ne se connecte pas
     au compte créé — l'administrateur reste sur sa propre session. */
  async function createTeamUser(d) {
    const u = { id: uid(), name: d.name, role: d.role, pin: d.pin, email: d.email || '', createdAt: new Date().toISOString() };
    const ok = await persist({
      users: [...users, u],
      journal: log({ type: 'compte', label: d.name, detail: `Compte créé par ${me.name} — ${ROLES[d.role].label}` }),
    });
    if (!ok) setStockageOk(false);
    return ok;
  }

  const can = (action) => {
    if (!me) return false;
    if (me.role === 'admin') return true;
    if (action === 'commande') return me.role === 'conducteur';
    if (action === 'appoint') return me.role === 'conducteur' || me.role === 'chantier';
    if (action === 'affaires') return me.role === 'conducteur';
    if (action === 'scan') return me.role === 'magasinier';
    if (action === 'parc') return me.role === 'magasinier' || me.role === 'conducteur';
    if (action === 'etat') return me.role === 'conducteur'; // corriger l'état / réformer le matériel : pas le magasinier
    if (action === 'stock') return false; // consommables et outillage : réservé à l'administrateur (bypass ci-dessus)
    return false;
  };

  /* ---------- création ---------- */

  function addUnit(d) {
    const u = { id: uid(), type: d.type, name: d.name, tag: d.tag, etat: 'propre', comment: '', lieu: 'Dépôt', dispo: true, dateRevision: d.dateRevision };
    persist({ units: [u, ...units], journal: log({ type: 'creation', label: `${d.name}${d.tag ? ` (${d.tag})` : ''}`, detail: `Matériel ajouté — révision valable jusqu'au ${frDate(addDays(d.dateRevision, REVISION_JOURS))}` }) });
    setModal(null);
  }

  function majRef(id, d) {
    persist({
      refs: refs.map((r) => (r.id === id ? { ...r, ...d } : r)),
      journal: log({ type: 'creation', label: d.name, detail: `Référence mise à jour — ${d.quantity} ${d.unit}, seuil ${d.seuil}` }),
    });
    setOpenRef(null);
  }

  function addRef(d) {
    const r = { id: uid(), name: d.name, unit: d.unit, quantity: d.quantity, seuil: d.seuil };
    persist({ refs: [r, ...refs], journal: log({ type: 'creation', label: d.name, detail: `Référence créée — ${d.quantity} ${d.unit}` }) });
    setModal(null);
  }

  function createCommande(d) {
    const affaire = affaires.find((a) => a.id === d.affaireId);
    const type = d.type || 'initiale';
    const prefixe = type === 'appoint' ? 'APP' : 'CMD';
    const rang = commandes.filter((c) => c.type === type).length + 1;
    const cmd = {
      id: uid(), num: `${prefixe}-${String(rang).padStart(3, '0')}`,
      type, affaireId: d.affaireId, chantier: libelleAffaire(affaire), adresse: affaire ? (affaire.adresse || '') : '',
      demandeur: me.name, demandeurRole: me.role,
      dateLivraison: d.dateLivraison, note: d.note,
      unitIds: d.unitIds, consos: d.consos, outils: d.outils || [], statut: 'a_preparer',
      charge: { unitIds: [], consos: {}, outils: {} }, repli: { units: {}, consos: {}, outils: {} },
      createdAt: new Date().toISOString(),
    };
    persist({
      commandes: [cmd, ...commandes],
      journal: log({
        type: 'commande', label: cmd.num,
        detail: `${TYPES_CMD[type].label} sur ${libelleAffaire(affaire)} — livraison demandée le ${frDate(d.dateLivraison)}`,
      }),
    });
    setModal(null); setFormCmd(null);
    setNotifier(cmd);
  }

  /* Liens documentaires (notice d'utilisation, fiche de révision) : de simples
     URL propres à chaque unité, l'application ne stocke pas de fichiers. */
  function modifierLiens(u, lienNotice, lienFicheRevision) {
    const nextUnits = units.map((x) => (x.id === u.id ? { ...x, lienNotice, lienFicheRevision } : x));
    persist({
      units: nextUnits,
      journal: log({ type: 'creation', label: `${u.name}${u.tag ? ` · ${u.tag}` : ''}`, detail: 'Liens documentaires mis à jour' }),
    });
  }

  /* ---------- réforme (matériel non réparable, hors service — réversible) ---------- */

  function reformer(u, comment) {
    const nextUnits = units.map((x) =>
      x.id === u.id ? { ...x, reforme: true, reformeComment: comment, reformeDate: todayISO(), dispo: false, lieu: 'Réformé' } : x
    );
    persist({
      units: nextUnits,
      journal: log({ type: 'reforme', label: `${u.name}${u.tag ? ` · ${u.tag}` : ''}`, detail: `Matériel réformé — ${comment}` }),
    });
    setOpenUnit(null);
  }

  function annulerReforme(u) {
    const perime = daysUntil(prochaineRevision(u)) < 0;
    const nextUnits = units.map((x) =>
      x.id === u.id
        ? { ...x, reforme: false, reformeComment: '', dispo: !perime, lieu: perime ? 'Quarantaine' : 'Dépôt' }
        : x
    );
    persist({
      units: nextUnits,
      journal: log({ type: 'reforme', label: `${u.name}${u.tag ? ` · ${u.tag}` : ''}`, detail: 'Réforme annulée — remis en circuit' }),
    });
    setOpenUnit(null);
  }

  /* ---------- masques attribués nominativement (page indépendante) ---------- */

  function attribuerMasque(d) {
    const m = {
      id: uid(), personne: d.personne, type: d.type, numeroInterne: d.numeroInterne,
      numeroMasque: d.numeroMasque, taille: d.taille, dateMiseEnService: d.dateMiseEnService,
      dateFitTest: d.dateFitTest || '', reforme: false,
    };
    persist({
      masquesAttribues: [m, ...masquesAttribues],
      journal: log({ type: 'masque', label: d.personne, detail: `Masque ${d.type} attribué — n° ${d.numeroMasque || d.numeroInterne}` }),
    });
  }

  function renouvelerMasque(m, d) {
    const nouveau = {
      id: uid(), personne: m.personne, type: m.type,
      numeroInterne: d.numeroInterne, numeroMasque: d.numeroMasque, taille: d.taille || m.taille,
      dateMiseEnService: d.dateMiseEnService, dateFitTest: d.dateFitTest || '', reforme: false,
    };
    const nextMasques = masquesAttribues.map((x) =>
      x.id === m.id ? { ...x, reforme: true, reformeMotif: 'Renouvelé', reformeDate: todayISO() } : x
    );
    persist({
      masquesAttribues: [nouveau, ...nextMasques],
      journal: log({ type: 'masque', label: m.personne, detail: `Masque ${m.type} renouvelé — nouveau n° ${d.numeroMasque || d.numeroInterne}` }),
    });
  }

  function declarerMasquePerdu(m, commentaire) {
    const nextMasques = masquesAttribues.map((x) =>
      x.id === m.id ? { ...x, reforme: true, reformeMotif: 'Perdu', reformeDate: todayISO(), reformeComment: commentaire } : x
    );
    persist({
      masquesAttribues: nextMasques,
      journal: log({ type: 'masque', label: m.personne, detail: `Masque ${m.type} déclaré perdu${commentaire ? ' — ' + commentaire : ''}` }),
    });
  }

  /* Le fit test suit sa propre échéance, indépendante de celle du masque
     lui-même : le renouveler ne touche à rien d'autre. */
  function renouvelerFitTest(m, date) {
    const nextMasques = masquesAttribues.map((x) => (x.id === m.id ? { ...x, dateFitTest: date } : x));
    persist({
      masquesAttribues: nextMasques,
      journal: log({
        type: 'masque', label: m.personne,
        detail: `Fit test enregistré pour le masque ${m.type} n° ${m.numeroMasque || m.numeroInterne} — prochaine échéance ${frDate(addDays(date, REVISION_JOURS))}`,
      }),
    });
  }

  /* Correction manuelle de l'état depuis la fiche matériel (hors scan de repli). */
  function changerEtat(u, etat, comment) {
    const nextUnits = units.map((x) => (x.id === u.id ? { ...x, etat, comment: comment || '' } : x));
    persist({
      units: nextUnits,
      journal: log({
        type: 'etat', label: `${u.name}${u.tag ? ` · ${u.tag}` : ''}`,
        detail: `État corrigé manuellement : ${ETATS[etat].label}${comment ? ' — ' + comment : ''}`,
      }),
    });
    setOpenUnit(null);
  }

  function reviser(u, note, facture) {
    const nextUnits = units.map((x) =>
      x.id === u.id
        ? { ...x, dateRevision: todayISO(), etat: 'propre', comment: '', lieu: 'Dépôt', dispo: true, derniereFacture: facture || '' }
        : x
    );
    persist({
      units: nextUnits,
      journal: log({
        type: 'revision', label: `${u.name}${u.tag ? ` · ${u.tag}` : ''}`,
        detail: `Révision effectuée${note ? ` — ${note}` : ''}${facture ? ` · Facture n° ${facture}` : ''}. Prochaine échéance ${frDate(addDays(todayISO(), REVISION_JOURS))}`,
      }),
    });
    setOpenUnit(null);
  }

  function majRole(u, role) {
    if (role === 'admin') return;                 // un seul administrateur
    persist({
      users: users.map((x) => (x.id === u.id ? { ...x, role } : x)),
      journal: log({ type: 'compte', label: u.name, detail: `Rôle modifié en ${ROLES[role].label}` }),
    });
  }

  function supprimerUser(u) {
    persist({
      users: users.filter((x) => x.id !== u.id),
      journal: log({ type: 'compte', label: u.name, detail: 'Compte supprimé' }),
    });
  }

  function addOutil(d) {
    persist({ outils: [{ id: uid(), name: d.name }, ...outils], journal: log({ type: 'creation', label: d.name, detail: 'Outillage ajouté au catalogue' }) });
    setModal(null);
  }

  /* ---------- import du parc ---------- */

  function importerParc() {
    const connus = new Set(units.map((u) => `${u.type}|${(u.tag || '').trim()}`));
    const nouveauxMateriel = PARC_INITIAL.filter((p) => !p.t || !connus.has(`${p.y}|${p.t.trim()}`)).map(uniteDepuisParc);
    const nouveauxVisiteur = MASQUES_VISITEUR_INITIAL.filter((p) => !connus.has(`Masques visiteur|${p.t.trim()}`)).map((p) => masqueDepuisImport(p, 'Masques visiteur'));
    const nouveauxPlomb = VA_PLOMB_INITIAL.filter((p) => !connus.has(`VA Plomb|${p.t.trim()}`)).map((p) => masqueDepuisImport(p, 'VA Plomb'));
    const nouveaux = [...nouveauxMateriel, ...nouveauxVisiteur, ...nouveauxPlomb];
    if (nouveaux.length === 0) return;
    persist({
      units: [...nouveaux, ...units],
      journal: log({ type: 'creation', label: 'Import du parc', detail: `${nouveaux.length} unité(s) ajoutée(s) depuis les fichiers de suivi` }),
    });
  }

  const parcManquant =
    PARC_INITIAL.filter((p) => p.t && !units.some((u) => u.type === p.y && (u.tag || '').trim() === p.t.trim())).length +
    MASQUES_VISITEUR_INITIAL.filter((p) => !units.some((u) => u.type === 'Masques visiteur' && (u.tag || '').trim() === p.t.trim())).length +
    VA_PLOMB_INITIAL.filter((p) => !units.some((u) => u.type === 'VA Plomb' && (u.tag || '').trim() === p.t.trim())).length;

  /* ---------- affaires ---------- */

  function addAffaire(d) {
    const a = { id: uid(), numero: d.numero, libelle: d.libelle, adresse: d.adresse || '', ouverte: true };
    persist({ affaires: [a, ...affaires], journal: log({ type: 'affaire', label: libelleAffaire(a), detail: 'Affaire ouverte' }) });
  }
  function toggleAffaire(a) {
    persist({
      affaires: affaires.map((x) => (x.id === a.id ? { ...x, ouverte: !x.ouverte } : x)),
      journal: log({ type: 'affaire', label: libelleAffaire(a), detail: a.ouverte ? 'Affaire clôturée' : 'Affaire rouverte' }),
    });
  }

  /* ---------- destinataires d'alerte ---------- */

  function addEmail(mail) {
    if (alertEmails.includes(mail)) return;
    persist({ alertEmails: [...alertEmails, mail], journal: log({ type: 'compte', label: mail, detail: "Ajouté à la liste d'alerte révisions" }) });
  }
  function removeEmail(mail) {
    persist({ alertEmails: alertEmails.filter((m) => m !== mail), journal: log({ type: 'compte', label: mail, detail: "Retiré de la liste d'alerte révisions" }) });
  }
  function marquerEnvoi(nb) {
    persist({ journal: log({ type: 'alerte', label: 'Alerte révisions', detail: `Envoyée à ${alertEmails.length} destinataire(s) — ${nb} matériel(s) concerné(s)` }) });
  }

  /* ---------- chargement ---------- */

  function validerChargement(cmd, charge) {
    const nextUnits = units.map((u) => (charge.unitIds.includes(u.id) ? { ...u, lieu: cmd.chantier, dispo: false } : u));
    const nextRefs = refs.map((r) => (charge.consos[r.id] ? { ...r, quantity: Math.max(0, r.quantity - charge.consos[r.id]) } : r));
    const nextCmds = commandes.map((c) => (c.id === cmd.id ? { ...c, statut: 'chargee', charge, chargeAt: new Date().toISOString(), chargePar: me.name } : c));
    const nb = Object.values(charge.consos).reduce((a, b) => a + b, 0);
    persist({
      units: nextUnits, refs: nextRefs, commandes: nextCmds,
      journal: log({ type: 'sortie', label: cmd.num, detail: `Camion chargé pour ${cmd.chantier} — ${charge.unitIds.length} matériel, ${nb} consommable(s)` }),
    });
    setScanMode(null);
  }

  /* ---------- repli ---------- */

  function validerRepli(cmd, repli) {
    let quarantaine = 0;
    const nextUnits = units.map((u) => {
      const r = repli.units[u.id];
      if (!r) return u;
      const perime = daysUntil(prochaineRevision(u)) < 0;
      const bloque = r.etat === 'hs' || perime;
      if (bloque) quarantaine++;
      return {
        ...u,
        etat: r.etat,
        comment: r.etat === 'hs' ? r.comment : perime ? 'Révision dépassée au retour de chantier' : '',
        lieu: bloque ? 'Quarantaine' : 'Dépôt',
        dispo: !bloque,
      };
    });
    const nextRefs = refs.map((r) => (repli.consos[r.id] ? { ...r, quantity: r.quantity + repli.consos[r.id] } : r));
    const nextCmds = commandes.map((c) => (c.id === cmd.id ? { ...c, statut: 'repliee', repli, repliAt: new Date().toISOString(), repliPar: me.name } : c));
    persist({
      units: nextUnits, refs: nextRefs, commandes: nextCmds,
      journal: log({ type: 'retour', label: cmd.num, detail: `Repli ${cmd.chantier} — ${Object.keys(repli.units).length} matériel rentré${quarantaine ? `, ${quarantaine} en quarantaine` : ''}` }),
    });
    setScanMode(null);
  }

  /* ---------- dérivés ---------- */

  const lowRefs = refs.filter((r) => r.quantity <= r.seuil);
  const enQuarantaine = units.filter((u) => ['hs', 'perime'].includes(etatUnite(u).key));
  const revisionProche = units.filter((u) => etatUnite(u).key === 'bientot');
  const aPreparer = commandes.filter((c) => c.statut === 'a_preparer');
  const appointsEnAttente = aPreparer.filter((c) => c.type === 'appoint');
  const enRetard = aPreparer.filter((c) => c.dateLivraison && c.dateLivraison < todayISO());
  /* Une commande est archivée dès que son affaire est clôturée — elle
     quitte alors l'écran Commandes pour l'onglet Archives. Une commande
     sans affaire retrouvée (donnée ancienne) reste visible par prudence. */
  const affaireOuverte = (c) => {
    const a = affaires.find((x) => x.id === c.affaireId);
    return !a || a.ouverte;
  };
  const commandesActives = commandes.filter(affaireOuverte);
  const commandesArchivees = commandes.filter((c) => !affaireOuverte(c));
  const aSignaler = units
    .filter((u) => !u.reforme && daysUntil(prochaineRevision(u)) <= ALERTE_JOURS)
    .sort((a, b) => daysUntil(prochaineRevision(a)) - daysUntil(prochaineRevision(b)));
  const masquesASignaler = masquesAttribues
    .filter((m) => !m.reforme && (
      daysUntil(addDays(m.dateMiseEnService || todayISO(), REVISION_JOURS)) <= ALERTE_JOURS ||
      (m.dateFitTest && daysUntil(addDays(m.dateFitTest, REVISION_JOURS)) <= ALERTE_JOURS)
    ))
    .sort((a, b) => daysUntil(addDays(a.dateMiseEnService, REVISION_JOURS)) - daysUntil(addDays(b.dateMiseEnService, REVISION_JOURS)));
  const current = commandes.find((c) => c.id === openCommande);

  if (loading) {
    return <div className="min-h-screen flex items-center justify-center" style={{ background: C.bg }}><Loader2 className="animate-spin" size={26} color={C.steel} /></div>;
  }

  if (!me) {
    return <LoginScreen users={users} stockageOk={stockageOk} onSignIn={signIn} onCreate={createUser} />;
  }

  if (formCmd) {
    return (
      <CommandePage type={formCmd} affaires={affaires} units={units} refs={refs} outils={outils}
        onCancel={() => setFormCmd(null)} onSave={createCommande} />
    );
  }

  if (current && scanMode) {
    return (
      <ScanSession
        mode={scanMode} commande={current} units={units} refs={refs} outils={outils}
        onCancel={() => setScanMode(null)}
        onValidate={(p) => (scanMode === 'chargement' ? validerChargement(current, p) : validerRepli(current, p))}
      />
    );
  }

  if (current) {
    return (
      <CommandeDetail
        commande={current} units={units} refs={refs} outils={outils} canScan={can('scan')} urlPublique={urlPublique}
        onBack={() => setOpenCommande(null)} onScan={setScanMode}
      />
    );
  }

  const famillesPresentes = Array.from(new Set(units.map((u) => u.type || 'Autre'))).sort();

  /* Filtres croisés : chaque pastille compte parmi ce que les AUTRES filtres
     laissent déjà passer, jamais sur l'ensemble brut du parc. Comme demandé :
     un matériel en quarantaine ne gonfle plus le total d'une famille — il
     apparaît à part, en sous-total, dans la pastille elle-même. */
  const enQuarantaineFn = (u) => ['hs', 'perime'].includes(etatUnite(u).key);
  const matchStatut = (u, f) => {
    const k = etatUnite(u).key;
    if (f === 'tous') return k !== 'reforme';
    if (f === 'dispo') return k === 'dispo' || k === 'bientot';
    if (f === 'chantier') return k === 'chantier';
    if (f === 'quarantaine') return k === 'hs' || k === 'perime';
    if (f === 'reforme') return k === 'reforme';
    return true;
  };
  const matchFamille = (u, t) => t === 'tous' || (u.type || 'Autre') === t;
  const rechercheParc = units.filter((u) => (u.name + ' ' + (u.tag || '')).toLowerCase().includes(search.toLowerCase()));

  let parcFiltered = rechercheParc
    .filter((u) => matchFamille(u, typeFilter))
    .filter((u) => matchStatut(u, parcFilter));

  if (parcFilter === 'tous') {
    /* Conforme d'abord, puis en s'approchant de l'échéance, jusqu'au périmé.
       Le HS (déclaré au repli) n'a pas de date pertinente : il ferme la liste. */
    parcFiltered = [...parcFiltered].sort((a, b) => {
      const ea = etatUnite(a), eb = etatUnite(b);
      const hsA = ea.key === 'hs' ? 1 : 0, hsB = eb.key === 'hs' ? 1 : 0;
      if (hsA !== hsB) return hsA - hsB;
      return eb.j - ea.j;
    });
  }

  return (
    <div className="min-h-screen pb-24" style={{ background: C.bg, color: C.ink }}>
      <header style={{ background: C.steel }} className="px-5 pt-5 pb-0 sticky top-0 z-20">
        <div className="flex items-center justify-between">
          <div className="flex items-center gap-2.5 min-w-0">
            <Logo height={30} />
            <h1 className="font-black truncate" style={{ color: '#fff', fontSize: 20, letterSpacing: '0.05em' }}>STOCK APII</h1>
          </div>
          <button onClick={() => setModal('profil')} className="flex items-center gap-1.5 text-xs" style={{ color: '#B3B3B1' }}>
            <UserRound size={14} />
            <span>{me.name}</span>
          </button>
        </div>
        <p className="text-[11px] mt-0.5" style={{ color: '#A3A3A1' }}>Connecté comme {ROLES[me.role].label}</p>
        <nav className="flex gap-4 mt-3 overflow-x-auto">
          {[
            { id: 'commandes', label: 'Commandes', icon: ClipboardList },
            { id: 'archives', label: 'Archives', icon: Archive },
            { id: 'parc', label: 'Parc', icon: Wrench },
            { id: 'conso', label: 'Consommables', icon: Package },
            { id: 'alertes', label: 'Alertes', icon: Mail },
            { id: 'masques', label: 'Masques', icon: Shield },
            { id: 'qr', label: 'QR', icon: QrCode },
            { id: 'journal', label: 'Journal', icon: History },
          ].map((t) => {
            const Icon = t.icon, on = tab === t.id;
            return (
              <button key={t.id} onClick={() => setTab(t.id)}
                className="flex items-center gap-1.5 pb-2.5 text-sm whitespace-nowrap"
                style={{ color: on ? '#fff' : '#A3A3A1', fontWeight: on ? 600 : 400, borderBottom: `2px solid ${on ? C.accent : 'transparent'}` }}>
                <Icon size={15} />{t.label}
              </button>
            );
          })}
        </nav>
      </header>

      {!stockageOk && (
        <div className="mx-5 mt-3 rounded-lg px-4 py-3 text-xs" style={{ background: C.redSoft, color: C.red }}>
          Aucune donnée n'est enregistrée dans cet aperçu. Utilisez le lien publié de l'application.
        </div>
      )}
      {saveError && stockageOk && (
        <div className="mx-5 mt-3 rounded-lg px-4 py-2 text-xs" style={{ background: C.redSoft, color: C.red }}>
          Échec de sauvegarde. Vérifiez la connexion, puis refaites l'action.
        </div>
      )}

      {/* ---------- COMMANDES ---------- */}
      {tab === 'commandes' && (
        <section className="px-5 mt-4">
          {appointsEnAttente.length > 0 && (
            <div className="rounded-lg px-4 py-3 mb-2 flex items-center gap-2 text-sm" style={{ background: C.greenSoft, color: C.green }}>
              <BellRing size={16} />
              {appointsEnAttente.length} demande{appointsEnAttente.length > 1 ? 's' : ''} d'appoint en attente
            </div>
          )}
          {enRetard.length > 0 && (
            <div className="rounded-lg px-4 py-3 mb-2 flex items-center gap-2 text-sm" style={{ background: C.redSoft, color: C.red }}>
              <AlertTriangle size={16} />
              {enRetard.length} commande{enRetard.length > 1 ? 's' : ''} dont la date de livraison est dépassée
            </div>
          )}
          {aPreparer.length > 0 && (
            <div className="rounded-lg px-4 py-3 mb-3 flex items-center gap-2 text-sm" style={{ background: C.steelSoft, color: C.steel }}>
              <Truck size={16} />{aPreparer.length} commande{aPreparer.length > 1 ? 's' : ''} à préparer
            </div>
          )}
          <AffairesInline
            affaires={affaires}
            commandes={commandes}
            canManage={can('affaires')}
            selected={affaireFilter}
            onSelect={setAffaireFilter}
            onAdd={addAffaire}
            onToggle={toggleAffaire}
          />
          {commandesActives.length === 0 ? (
            <Empty icon={ClipboardList} title="Aucune commande"
              text={can('commande') ? "Créez une commande : le magasinier la préparera en scannant." : "Le chargé d'affaires n'a pas encore créé de commande."}
              cta={can('appoint') ? (can('commande') ? 'Créer une commande' : "Demander un appoint") : null}
              onCta={() => (can('commande') ? setModal('choixCmd') : setFormCmd('appoint'))} />
          ) : (
            <div className="flex flex-col gap-2">
              {commandesActives
                .filter((c) => affaireFilter === 'toutes' || c.affaireId === affaireFilter)
                .map((c) => <CommandeCarte key={c.id} c={c} onOpen={() => setOpenCommande(c.id)} />)}
            </div>
          )}
        </section>
      )}

      {/* ---------- ARCHIVES ---------- */}
      {tab === 'archives' && (
        <section className="px-5 mt-4">
          <p className="text-xs mb-3" style={{ color: C.soft }}>
            Commandes des affaires clôturées — elles n'apparaissent plus dans l'onglet Commandes.
          </p>
          {commandesArchivees.length === 0 ? (
            <Empty icon={Archive} title="Aucune archive"
              text="Les commandes des affaires que vous clôturez arriveront ici." />
          ) : (
            <div className="flex flex-col gap-2">
              {commandesArchivees.map((c) => <CommandeCarte key={c.id} c={c} onOpen={() => setOpenCommande(c.id)} />)}
            </div>
          )}
        </section>
      )}

      {/* ---------- PARC ---------- */}
      {tab === 'parc' && (
        <section className="px-5 mt-4">
          {(enQuarantaine.length > 0 || revisionProche.length > 0) && (
            <div className="rounded-lg px-4 py-3 mb-3 text-sm flex flex-col gap-1"
              style={{ background: enQuarantaine.length ? C.redSoft : C.amberSoft, color: enQuarantaine.length ? C.red : C.amber }}>
              {enQuarantaine.length > 0 && (
                <span className="flex items-center gap-2"><AlertTriangle size={15} />{enQuarantaine.length} matériel en quarantaine</span>
              )}
              {revisionProche.length > 0 && (
                <span className="flex items-center gap-2"><CalendarClock size={15} />{revisionProche.length} révision{revisionProche.length > 1 ? 's' : ''} à prévoir sous {ALERTE_JOURS} jours</span>
              )}
            </div>
          )}

          {parcManquant > 0 && can('parc') && (
            <button onClick={importerParc} className="w-full rounded-lg px-4 py-3 mb-3 text-sm font-semibold text-left"
              style={{ background: C.accentSoft, border: `1px solid ${C.accent}`, color: C.accentInk }}>
              Importer {parcManquant} unité{parcManquant > 1 ? 's' : ''} du fichier de suivi matériel
              <span className="block text-[11px] font-normal mt-0.5" style={{ color: C.soft }}>
                Les numéros de série déjà présents ne seront pas dupliqués.
              </span>
            </button>
          )}
          <div className="flex items-center gap-2 rounded-lg px-3 py-2 mb-3" style={{ background: C.surface, border: `1px solid ${C.border}` }}>
            <Search size={15} color={C.soft} />
            <input value={search} onChange={(e) => setSearch(e.target.value)} placeholder="Rechercher un matériel…" className="flex-1 outline-none text-sm bg-transparent" />
          </div>

          {/* Familles : le nombre principal exclut la quarantaine ; le badge
              rouge donne le sous-total en quarantaine pour cette famille. */}
          {famillesPresentes.length > 0 && (
            <div className="flex gap-2 mb-2 overflow-x-auto">
              {['tous', ...famillesPresentes].map((t) => {
                const on = typeFilter === t;
                const poolFamille = (t === 'tous' ? rechercheParc : rechercheParc.filter((u) => (u.type || 'Autre') === t))
                  .filter((u) => !u.reforme);
                const n = poolFamille.filter((u) => !enQuarantaineFn(u)).length;
                const q = poolFamille.filter(enQuarantaineFn).length;
                return (
                  <button key={t} onClick={() => setTypeFilter(t)}
                    className="px-3 py-1.5 rounded-full text-xs whitespace-nowrap flex items-center gap-1.5"
                    style={{
                      background: on ? C.accentSoft : C.surface,
                      color: on ? C.accentInk : C.soft,
                      fontWeight: on ? 600 : 400,
                      border: `1px solid ${on ? C.accent : C.border}`,
                    }}>
                    <span>{t === 'tous' ? 'Toutes familles' : t} ({n})</span>
                    {q > 0 && (
                      <span className="rounded-full px-1.5 py-0.5" style={{ background: C.redSoft, color: C.red, fontSize: 10, fontWeight: 700 }}>
                        +{q} quar.
                      </span>
                    )}
                  </button>
                );
              })}
            </div>
          )}

          {/* État : les compteurs se recalculent sur la famille sélectionnée ci-dessus,
              pour rester justes quand on cherche par exemple un extracteur précis. */}
          <div className="flex gap-2 mb-4 overflow-x-auto">
            {[
              { id: 'tous', label: 'Tout' },
              { id: 'dispo', label: 'Disponible' },
              { id: 'chantier', label: 'Sur chantier' },
              { id: 'quarantaine', label: 'Quarantaine' },
              { id: 'reforme', label: 'Réformé' },
            ].map((f) => {
              const n = rechercheParc.filter((u) => matchFamille(u, typeFilter) && matchStatut(u, f.id)).length;
              return (
                <button key={f.id} onClick={() => setParcFilter(f.id)}
                  className="px-3 py-1.5 rounded-full text-xs font-medium whitespace-nowrap"
                  style={{
                    background: parcFilter === f.id ? C.steel : C.surface,
                    color: parcFilter === f.id ? '#fff' : C.soft,
                    border: `1px solid ${parcFilter === f.id ? C.steel : C.border}`,
                  }}>
                  {f.label} ({n})
                </button>
              );
            })}
          </div>

          {units.length === 0 ? (
            <Empty icon={Wrench} title="Parc vide" text="Ajoutez vos unités de matériel pour générer leurs QR et suivre leurs révisions."
              cta={can('parc') ? 'Ajouter du matériel' : null} onCta={() => setModal('unite')} />
          ) : parcFiltered.length === 0 ? (
            <p className="text-sm text-center py-10" style={{ color: C.soft }}>Aucun matériel dans ce filtre.</p>
          ) : (
            <div className="flex flex-col gap-2">
              {parcFiltered.map((u) => {
                const e = etatUnite(u);
                return (
                  <button key={u.id} onClick={() => setOpenUnit(u.id)} className="text-left rounded-lg px-4 py-3"
                    style={{ background: C.surface, border: `1px solid ${C.border}`, borderLeft: `4px solid ${e.color}` }}>
                    <div className="flex items-start justify-between gap-3">
                      <div className="min-w-0">
                        <p className="text-sm font-semibold truncate">{u.name}</p>
                        <p className="text-xs" style={{ color: C.soft }}>
                          {u.type ? `${u.type} · ` : ''}{u.tag ? `${u.tag} · ` : ''}{u.lieu}
                        </p>
                      </div>
                      <span className="text-[11px] font-semibold rounded px-2 py-1 flex-shrink-0" style={{ background: e.soft, color: e.color }}>
                        {e.key === 'reforme' ? 'Réformé' : e.key === 'chantier' ? 'Sur chantier' : e.key === 'hs' ? 'HS' : e.key === 'perime' ? 'Périmé' : e.key === 'bientot' ? `J−${e.j}` : 'Dispo'}
                      </span>
                    </div>
                    <p className="text-[11px] mt-1.5" style={{ color: e.j < 0 ? C.red : C.soft }}>
                      Révision à faire avant le {frDate(e.next)}
                      {u.comment ? ` · ${u.comment}` : ''}
                    </p>
                  </button>
                );
              })}
            </div>
          )}
        </section>
      )}

      {/* ---------- CONSOMMABLES ---------- */}
      {tab === 'conso' && (
        <section className="px-5 mt-4">
          <div className="flex gap-2 mb-3">
            {[
              { id: 'conso', label: `Consommables (${refs.length})`, icon: Package },
              { id: 'outils', label: `Outillage (${outils.length})`, icon: Hammer },
            ].map((t) => {
              const Icon = t.icon, on = consoVue === t.id;
              return (
                <button key={t.id} onClick={() => setConsoVue(t.id)}
                  className="flex-1 rounded-lg py-2 text-xs font-semibold flex items-center justify-center gap-1.5"
                  style={{ background: on ? C.steel : C.surface, color: on ? '#fff' : C.soft, border: `1px solid ${on ? C.steel : C.border}` }}>
                  <Icon size={14} />{t.label}
                </button>
              );
            })}
          </div>

          {consoVue === 'outils' ? (
            <>
              <p className="text-xs mb-3" style={{ color: C.soft }}>
                Outillage de chantier : ni stock ni suivi de révision. Ces articles se cochent simplement sur les commandes.
              </p>
              <div className="flex flex-col gap-2">
                {outils.length === 0 && <p className="text-xs" style={{ color: C.soft }}>Aucun outillage enregistré.</p>}
                {outils.map((o) => (
                  <div key={o.id} className="rounded-lg px-4 py-2.5 text-sm" style={{ background: C.surface, border: `1px solid ${C.border}` }}>
                    {o.name}
                  </div>
                ))}
              </div>
            </>
          ) : (
          <>
          {lowRefs.length > 0 && (
            <div className="rounded-lg px-4 py-3 mb-3 flex items-center gap-2 text-sm" style={{ background: C.redSoft, color: C.red }}>
              <AlertTriangle size={16} />{lowRefs.length} référence{lowRefs.length > 1 ? 's' : ''} sous le seuil
            </div>
          )}
          {refs.length === 0 ? (
            <Empty icon={Package} title="Aucune référence" text="Créez vos références de consommables pour les commander et les scanner."
              cta={can('stock') ? 'Ajouter une référence' : null} onCta={() => setModal('ref')} />
          ) : (
            <div className="flex flex-col gap-2">
              {refs.map((r) => {
                const low = r.quantity <= r.seuil;
                return (
                  <button key={r.id} onClick={() => can('stock') && setOpenRef(r.id)}
                    className="text-left rounded-lg px-4 py-3 flex items-center justify-between gap-3"
                    style={{ background: C.surface, border: `1px solid ${C.border}`, borderLeft: low ? `4px solid ${C.accent}` : undefined }}>
                    <p className="text-sm font-semibold truncate">{r.name}</p>
                    <div className="text-right flex-shrink-0">
                      <p className="text-base font-bold" style={{ color: low ? C.accentInk : C.ink }}>
                        {r.quantity} <span className="text-xs font-normal" style={{ color: C.soft }}>{r.unit}</span>
                      </p>
                      <p className="text-[11px]" style={{ color: C.soft }}>seuil {r.seuil}</p>
                    </div>
                  </button>
                );
              })}
            </div>
          )}
          </>
          )}
        </section>
      )}

      {/* ---------- ALERTES ---------- */}
      {tab === 'alertes' && (
        <AlertesPanel
          units={aSignaler}
          masques={masquesASignaler}
          emails={alertEmails}
          users={users}
          isAdmin={me.role === 'admin'}
          onAdd={addEmail}
          onRemove={removeEmail}
          onSent={marquerEnvoi}
        />
      )}

      {/* ---------- MASQUES ATTRIBUÉS ---------- */}
      {tab === 'masques' && (
        <MasquesAttribuesPanel
          masques={masquesAttribues}
          canGerer={can('etat')}
          onAttribuer={attribuerMasque}
          onRenouveler={renouvelerMasque}
          onPerdu={declarerMasquePerdu}
          onRenouvelerFitTest={renouvelerFitTest}
        />
      )}

      {/* ---------- QR ---------- */}
      {tab === 'qr' && (
        <QrPanel
          units={units} refs={refs} urlPublique={urlPublique}
          vue={qrVue} setVue={(v) => { setQrVue(v); setQrPage(0); }}
          search={qrSearch} setSearch={(v) => { setQrSearch(v); setQrPage(0); }}
          page={qrPage} setPage={setQrPage}
        />
      )}

      {/* ---------- JOURNAL ---------- */}
      {tab === 'journal' && (
        <section className="px-5 mt-4">
          {journal.length === 0 ? (
            <p className="text-sm text-center py-12" style={{ color: C.soft }}>Aucun mouvement enregistré.</p>
          ) : (
            <div className="flex flex-col gap-2">
              {journal.map((j) => {
                const tone =
                  j.type === 'sortie' ? { bg: C.accentSoft, fg: C.accentInk, Icon: Truck }
                    : j.type === 'retour' ? { bg: C.greenSoft, fg: C.green, Icon: Undo2 }
                    : j.type === 'revision' ? { bg: C.amberSoft, fg: C.amber, Icon: CalendarClock }
                    : j.type === 'commande' ? { bg: C.steelSoft, fg: C.steel, Icon: ClipboardList }
                    : j.type === 'alerte' ? { bg: C.amberSoft, fg: C.amber, Icon: Mail }
                    : j.type === 'affaire' ? { bg: C.steelSoft, fg: C.steelMid, Icon: Briefcase }
                    : j.type === 'reforme' ? { bg: C.redSoft, fg: C.red, Icon: Archive }
                    : j.type === 'etat' ? { bg: C.amberSoft, fg: C.amber, Icon: Droplets }
                    : j.type === 'compte' ? { bg: C.steelSoft, fg: C.steelMid, Icon: UserRound }
                    : { bg: C.steelSoft, fg: C.steelMid, Icon: Plus };
                const Icon = tone.Icon;
                return (
                  <div key={j.id} className="flex items-start gap-3 rounded-lg px-3 py-2.5" style={{ background: C.surface, border: `1px solid ${C.border}` }}>
                    <div className="rounded-full flex items-center justify-center flex-shrink-0" style={{ width: 28, height: 28, background: tone.bg }}>
                      <Icon size={13} color={tone.fg} />
                    </div>
                    <div className="flex-1 min-w-0">
                      <p className="text-sm font-medium">{j.label}</p>
                      <p className="text-xs" style={{ color: C.soft }}>{j.detail}</p>
                      <p className="text-[11px] mt-0.5" style={{ color: C.soft }}>par {j.par || '—'}</p>
                    </div>
                    <span className="text-[11px] flex-shrink-0" style={{ color: C.soft }}>{relTime(j.date)}</span>
                  </div>
                );
              })}
            </div>
          )}
        </section>
      )}

      {((tab === 'commandes' && can('appoint')) || (tab === 'parc' && can('parc')) || (tab === 'conso' && can('stock'))) && (
        <button onClick={() => {
          if (tab === 'commandes') { if (can('commande')) setModal('choixCmd'); else setFormCmd('appoint'); }
          else setModal(tab === 'parc' ? 'unite' : consoVue === 'outils' ? 'outil' : 'ref');
        }}
          className="fixed bottom-6 right-6 rounded-full flex items-center justify-center shadow-lg z-30"
          style={{ width: 54, height: 54, background: C.accent }} aria-label="Ajouter">
          <Plus size={24} color={C.ink} />
        </button>
      )}

      {modal === 'unite' && <UnitForm onClose={() => setModal(null)} onSave={addUnit} />}
      {modal === 'ref' && <RefForm onClose={() => setModal(null)} onSave={addRef} />}
      {modal === 'outil' && <OutilForm onClose={() => setModal(null)} onSave={addOutil} />}
      {modal === 'profil' && (
        <ProfilSheet me={me} users={users} urlPubliqueActuelle={urlPublique} onUrlPublique={(v) => persist({ urlPublique: v })}
          onClose={() => setModal(null)}
          onRole={majRole} onSupprimer={supprimerUser} onSignOut={signOut} onCreate={createTeamUser} />
      )}
      {openRef && (
        <RefForm reference={refs.find((r) => r.id === openRef)}
          onClose={() => setOpenRef(null)}
          onSave={(d) => majRef(openRef, d)} />
      )}
      {modal === 'choixCmd' && (
        <Sheet title="Nouvelle commande" onClose={() => setModal(null)}>
          <button onClick={() => { setModal(null); setFormCmd('initiale'); }} className="w-full rounded-lg py-3 mb-2 text-sm font-semibold flex items-center justify-center gap-2"
            style={{ background: C.steel, color: '#fff' }}>
            <ClipboardList size={16} /> Commande initiale
          </button>
          <button onClick={() => { setModal(null); setFormCmd('appoint'); }} className="w-full rounded-lg py-3 text-sm font-semibold flex items-center justify-center gap-2"
            style={{ background: C.green, color: '#fff' }}>
            <BellRing size={16} /> Commande d'appoint
          </button>
        </Sheet>
      )}
      {notifier && (
        <NotifierSheet commande={notifier} users={users} units={units} refs={refs}
          onClose={() => { const id = notifier.id; setNotifier(null); setOpenCommande(id); }}
          onSent={(c, n) => persist({ journal: log({ type: 'alerte', label: c.num, detail: `${TYPES_CMD[c.type].label} — notification envoyée à ${n} destinataire(s)` }) })} />
      )}

      {openUnit && (
        <UnitSheet
          unit={units.find((u) => u.id === openUnit)}
          journal={journal}
          commandes={commandes}
          canRevise={can('parc')}
          canEtat={can('etat')}
          urlPublique={urlPublique}
          onClose={() => setOpenUnit(null)}
          onRevise={reviser}
          onReformer={reformer}
          onAnnulerReforme={annulerReforme}
          onChangerEtat={changerEtat}
          onModifierLiens={modifierLiens}
        />
      )}
    </div>
  );
}

/* =================== CONNEXION =================== */

function LoginScreen({ users, stockageOk, onSignIn, onCreate }) {
  const premier = users.length === 0;
  /* Seul le tout premier profil (l'administrateur) peut se créer lui-même ici.
     Une fois l'administrateur en place, les autres comptes sont créés par lui
     depuis "Mon profil" — pas de création libre sur cette page publique. */
  const rolesOuverts = Object.entries(ROLES).filter(([k]) => premier && k === 'admin');
  const [step, setStep] = useState(premier ? 'new' : 'pick');
  const [selected, setSelected] = useState(null);
  const [pin, setPin] = useState('');
  const [error, setError] = useState('');
  const [name, setName] = useState('');
  const [email, setEmail] = useState('');
  const [role, setRole] = useState(premier ? 'admin' : null);
  const [newPin, setNewPin] = useState('');
  const mailOk = email.trim() === '' || /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email.trim());

  function tryPin() {
    if (pin === selected.pin) { onSignIn(selected); }
    else { setError('Code incorrect'); setPin(''); }
  }

  return (
    <div className="min-h-screen flex flex-col" style={{ background: C.steel }}>
      <div className="px-6 pt-14 pb-8">
        <Logo height={58} />
        <h1 className="font-black mt-4" style={{ color: '#fff', fontSize: 30, letterSpacing: '0.05em', lineHeight: 1 }}>STOCK<br />APII</h1>
        <p className="text-sm mt-3" style={{ color: '#B3B3B1' }}>Matériel, consommables et commandes de chantier.</p>
        <p className="text-[11px] mt-1" style={{ color: '#8A8A88' }}>Version {VERSION_APP}</p>
      </div>

      <div className="flex-1 rounded-t-3xl px-6 pt-6 pb-10" style={{ background: C.bg }}>
        {!stockageOk && (
          <div className="rounded-lg px-4 py-3 mb-4 text-sm" style={{ background: C.redSoft, color: C.red }}>
            <p className="font-semibold mb-1">Rien ne sera enregistré ici</p>
            <p className="text-xs">
              L'enregistrement partagé ne fonctionne que sur le lien publié de l'application.
              Un compte créé depuis cet aperçu disparaîtra. Ouvrez le lien publié avant de continuer.
            </p>
          </div>
        )}
        {step === 'pick' && (
          <>
            <h2 className="text-base font-bold mb-1">Qui êtes-vous ?</h2>
            <p className="text-xs mb-4" style={{ color: C.soft }}>Sélectionnez votre profil pour retrouver vos droits.</p>
            <div className="flex flex-col gap-2">
              {users.map((u) => (
                <button key={u.id} onClick={() => { setSelected(u); setPin(''); setError(''); setStep('pin'); }}
                  className="text-left rounded-lg px-4 py-3 flex items-center gap-3"
                  style={{ background: C.surface, border: `1px solid ${C.border}` }}>
                  <div className="rounded-full flex items-center justify-center flex-shrink-0"
                    style={{ width: 36, height: 36, background: ROLES[u.role].color }}>
                    <span className="text-sm font-bold" style={{ color: onColor(ROLES[u.role].color) }}>{u.name.slice(0, 2).toUpperCase()}</span>
                  </div>
                  <div>
                    <p className="text-sm font-semibold">{u.name}</p>
                    <p className="text-xs" style={{ color: C.soft }}>{ROLES[u.role].label}</p>
                  </div>
                </button>
              ))}
            </div>
            <p className="text-xs mt-4" style={{ color: C.soft }}>
              Pas encore de profil ? Demandez à l'administrateur de vous en créer un.
            </p>
          </>
        )}

        {step === 'pin' && (
          <>
            <button onClick={() => setStep('pick')} className="flex items-center gap-1 text-sm mb-4" style={{ color: C.soft }}>
              <ArrowLeft size={16} /> Changer de profil
            </button>
            <h2 className="text-base font-bold">{selected.name}</h2>
            <p className="text-xs mb-4" style={{ color: C.soft }}>{ROLES[selected.role].label} — saisissez votre code à 4 chiffres.</p>
            <input
              type="password" inputMode="numeric" maxLength={4} autoFocus
              value={pin}
              onChange={(e) => { setPin(e.target.value.replace(/\D/g, '')); setError(''); }}
              className="w-full text-center outline-none rounded-lg mb-3"
              style={{ border: `1px solid ${error ? C.red : C.border}`, padding: '14px', fontSize: 26, letterSpacing: '0.6em', background: C.surface }}
              placeholder="••••"
            />
            {error && <p className="text-xs mb-3" style={{ color: C.red }}>{error}</p>}
            <PrimaryButton disabled={pin.length !== 4} onClick={tryPin}>Se connecter</PrimaryButton>
          </>
        )}

        {step === 'new' && (
          <>
            {users.length > 0 && (
              <button onClick={() => setStep('pick')} className="flex items-center gap-1 text-sm mb-4" style={{ color: C.soft }}>
                <ArrowLeft size={16} /> Retour
              </button>
            )}
            <h2 className="text-base font-bold mb-1">Créer un profil</h2>
            <p className="text-xs mb-4" style={{ color: C.soft }}>
              {premier
                ? 'Premier profil : ce sera le compte administrateur, réservé au responsable. Il ne pourra pas être dupliqué.'
                : "Le profil sera visible par toute l'équipe."}
            </p>
            <Field label="Nom et prénom">
              <input style={inputStyle} value={name} onChange={(e) => setName(e.target.value)} placeholder="Ex. Karim B." />
            </Field>
            <Field label="Adresse e-mail (pour recevoir les notifications)">
              <input type="email" style={{ ...inputStyle, borderColor: mailOk ? C.border : C.red }}
                value={email} onChange={(e) => setEmail(e.target.value)} placeholder="prenom.nom@apii.fr" />
            </Field>
            <Field label={role ? 'Rôle' : 'Rôle — à choisir'}>
              <div className="flex flex-col gap-2">
                {rolesOuverts.map(([k, r]) => {
                  const on = role === k;
                  return (
                    <button key={k} onClick={() => setRole(k)} className="text-left rounded-lg px-3 py-2.5 flex items-center justify-between gap-2"
                      style={{ background: on ? C.surface : '#FCFBF9', border: `2px solid ${on ? r.color : C.border}` }}>
                      <div className="min-w-0">
                        <p className="text-sm font-semibold" style={{ color: on ? r.color : C.ink }}>{r.label}</p>
                        <p className="text-[11px]" style={{ color: C.soft }}>{r.desc}</p>
                      </div>
                      <div className="rounded-full flex items-center justify-center flex-shrink-0"
                        style={{ width: 22, height: 22, border: `2px solid ${on ? r.color : C.border}`, background: on ? r.color : 'transparent' }}>
                        {on && <Check size={13} color={onColor(r.color)} />}
                      </div>
                    </button>
                  );
                })}
              </div>
            </Field>
            <Field label="Code à 4 chiffres">
              <input type="password" inputMode="numeric" maxLength={4} style={inputStyle}
                value={newPin} onChange={(e) => setNewPin(e.target.value.replace(/\D/g, ''))} placeholder="••••" />
            </Field>
            <p className="text-[11px] mb-3" style={{ color: C.soft }}>
              Ce code sert à identifier qui fait quoi dans le journal. Ce n'est pas une sécurité forte : ne l'utilisez pas pour protéger des données confidentielles.
            </p>
            {!role && (
              <p className="text-xs mb-3" style={{ color: C.red }}>
                Choisissez votre rôle : il détermine ce que vous pourrez faire dans l'application.
              </p>
            )}
            <PrimaryButton disabled={!name.trim() || newPin.length !== 4 || !mailOk || !stockageOk || !role}
              onClick={() => onCreate({ name: name.trim(), email: email.trim().toLowerCase(), role, pin: newPin })}>
              Créer et se connecter
            </PrimaryButton>
          </>
        )}
      </div>
    </div>
  );
}


/* =================== PROFIL ET ÉQUIPE =================== */

const DROITS = {
  conducteur: ['Ouvrir et clôturer les affaires', 'Créer les commandes et les appoints', 'Gérer le matériel'],
  magasinier: ['Scanner les chargements et les replis', 'Gérer le matériel', 'Enregistrer les révisions'],
  chantier: ["Demander des commandes d'appoint", 'Consulter le parc et les commandes'],
  admin: ['Tous les droits', "Gérer les comptes de l'équipe", 'Gérer le stock de consommables et l\'outillage', "Gérer la liste d'alerte révisions"],
};

function UrlPubliqueForm({ valeur, onSave }) {
  const [saisie, setSaisie] = useState(valeur || '');
  const [modifie, setModifie] = useState(false);
  return (
    <div className="mb-4">
      <p className="text-xs mb-2" style={{ color: C.soft }}>
        Si renseigné, chaque QR devient une vraie adresse : un smartphone qui le scanne avec son appareil photo
        ouvre directement la fiche du matériel, avec ses liens. Laissez vide pour garder le fonctionnement actuel
        (le scan ne marche alors que depuis l'application).
      </p>
      <div className="rounded-lg px-3 py-2 mb-2 text-xs" style={{ background: C.amberSoft, color: C.amber }}>
        Attention : si vous republiez l'application sur une nouvelle adresse, ce lien devient faux et les étiquettes
        déjà imprimées ne s'ouvriront plus toutes seules. À réserver à une adresse stable (hébergement définitif).
      </div>
      <input style={inputStyle} value={saisie}
        onChange={(e) => { setSaisie(e.target.value); setModifie(true); }}
        placeholder="https://stock.apii-mtp.com" />
      {modifie && (
        <button onClick={() => { onSave(saisie.trim()); setModifie(false); }}
          className="w-full mt-2 rounded-lg py-2 text-sm font-semibold" style={{ background: C.steel, color: '#fff' }}>
          Enregistrer le lien public
        </button>
      )}
    </div>
  );
}

function ProfilSheet({ me, users, urlPubliqueActuelle, onUrlPublique, onClose, onRole, onSupprimer, onSignOut, onCreate }) {
  const isAdmin = me.role === 'admin';
  const [confirmer, setConfirmer] = useState(null);
  const [ajout, setAjout] = useState(false);
  const [nom, setNom] = useState('');
  const [mail, setMail] = useState('');
  const [role, setRole] = useState(null);
  const [pinCode, setPinCode] = useState('');
  const mailOk = mail.trim() === '' || /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(mail.trim());
  const peutCreer = nom.trim() && mailOk && role && pinCode.length === 4;

  function reinitialiserAjout() {
    setAjout(false); setNom(''); setMail(''); setRole(null); setPinCode('');
  }

  return (
    <Sheet title="Mon profil" onClose={onClose}>
      <div className="rounded-lg px-4 py-3 mb-3" style={{ background: C.steelSoft }}>
        <p className="text-sm font-bold">{me.name}</p>
        <p className="text-xs" style={{ color: C.soft }}>{ROLES[me.role].label}{me.email ? ` · ${me.email}` : ''}</p>
      </div>
      <ul className="mb-4">
        {DROITS[me.role].map((d) => (
          <li key={d} className="text-xs flex items-start gap-1.5 mb-1" style={{ color: C.soft }}>
            <Check size={13} color={C.green} style={{ flexShrink: 0, marginTop: 1 }} />{d}
          </li>
        ))}
      </ul>

      {isAdmin && (
        <>
          <SectionTitle icon={UserRound} label={`Équipe (${users.length})`} />
          <div className="flex flex-col gap-2 mb-4">
            {users.filter((u) => u.id !== me.id).length === 0 && (
              <p className="text-xs" style={{ color: C.soft }}>Aucun autre compte pour l'instant.</p>
            )}
            {users.filter((u) => u.id !== me.id).map((u) => (
              <div key={u.id} className="rounded-lg px-3 py-2.5" style={{ background: C.surface, border: `1px solid ${C.border}` }}>
                <div className="flex items-center justify-between gap-2">
                  <div className="min-w-0">
                    <p className="text-sm font-semibold truncate">{u.name}</p>
                    {u.email && <p className="text-[11px] truncate" style={{ color: C.soft }}>{u.email}</p>}
                  </div>
                  <button onClick={() => setConfirmer(confirmer === u.id ? null : u.id)}
                    className="text-[11px] font-semibold flex-shrink-0" style={{ color: C.red }}>
                    {confirmer === u.id ? 'Annuler' : 'Supprimer'}
                  </button>
                </div>
                <select value={u.role} onChange={(e) => onRole(u, e.target.value)}
                  className="w-full mt-2 rounded-md px-2 py-1.5 text-xs outline-none"
                  style={{ background: '#FCFBF9', border: `1px solid ${C.border}`, color: C.ink }}>
                  {Object.entries(ROLES).filter(([k]) => k !== 'admin').map(([k, r]) => (
                    <option key={k} value={k}>{r.label}</option>
                  ))}
                </select>
                {confirmer === u.id && (
                  <button onClick={() => { onSupprimer(u); setConfirmer(null); }}
                    className="w-full mt-2 rounded-md py-1.5 text-xs font-semibold" style={{ background: C.red, color: '#fff' }}>
                    Confirmer la suppression de {u.name}
                  </button>
                )}
              </div>
            ))}
          </div>
          <p className="text-[11px] mb-4" style={{ color: C.soft }}>
            Le rôle d'administrateur ne peut pas être attribué : il reste sur ce compte.
          </p>

          {ajout ? (
            <div className="rounded-lg px-3 py-3 mb-4" style={{ background: C.surface, border: `1px dashed ${C.border}` }}>
              <Field label="Nom et prénom">
                <input style={inputStyle} value={nom} onChange={(e) => setNom(e.target.value)} placeholder="Ex. Karim B." />
              </Field>
              <Field label="Adresse e-mail (optionnel)">
                <input type="email" style={{ ...inputStyle, borderColor: mailOk ? C.border : C.red }}
                  value={mail} onChange={(e) => setMail(e.target.value)} placeholder="prenom.nom@apii.fr" />
              </Field>
              <Field label="Rôle">
                <div className="flex flex-col gap-2">
                  {Object.entries(ROLES).filter(([k]) => k !== 'admin').map(([k, r]) => {
                    const on = role === k;
                    return (
                      <button key={k} onClick={() => setRole(k)} className="text-left rounded-lg px-3 py-2 flex items-center justify-between gap-2"
                        style={{ background: on ? '#fff' : '#FCFBF9', border: `2px solid ${on ? r.color : C.border}` }}>
                        <span className="text-sm font-semibold" style={{ color: on ? r.color : C.ink }}>{r.label}</span>
                        {on && <Check size={14} color={r.color} />}
                      </button>
                    );
                  })}
                </div>
              </Field>
              <Field label="Code à 4 chiffres">
                <input type="password" inputMode="numeric" maxLength={4} style={inputStyle}
                  value={pinCode} onChange={(e) => setPinCode(e.target.value.replace(/\D/g, ''))} placeholder="••••" />
              </Field>
              <div className="flex gap-2">
                <button onClick={reinitialiserAjout} className="flex-1 rounded-lg py-2 text-sm font-semibold" style={{ background: C.steelSoft, color: C.soft }}>
                  Annuler
                </button>
                <button disabled={!peutCreer}
                  onClick={() => { onCreate({ name: nom.trim(), email: mail.trim().toLowerCase(), role, pin: pinCode }); reinitialiserAjout(); }}
                  className="flex-1 rounded-lg py-2 text-sm font-semibold"
                  style={{ background: peutCreer ? C.accent : C.border, color: peutCreer ? C.ink : C.soft }}>
                  Créer le compte
                </button>
              </div>
            </div>
          ) : (
            <button onClick={() => setAjout(true)} className="text-sm mb-4 flex items-center gap-1.5 font-semibold" style={{ color: C.accentInk }}>
              <UserRoundPlus size={16} /> Ajouter un compte
            </button>
          )}

          <SectionTitle icon={QrCode} label="Lien public de l'application" />
          <UrlPubliqueForm valeur={urlPubliqueActuelle} onSave={onUrlPublique} />
        </>
      )}

      <PrimaryButton color={C.steel} onClick={onSignOut}>
        <span className="flex items-center justify-center gap-2"><LogOut size={16} /> Se déconnecter</span>
      </PrimaryButton>
      <p className="text-[11px] text-center mt-3" style={{ color: C.soft }}>
        Application version {VERSION_APP}
      </p>
    </Sheet>
  );
}

/* =================== PLANCHE D'ÉTIQUETTES QR =================== */

const QR_PAR_PAGE = 12;

function QrPanel({ units, refs, urlPublique, vue, setVue, search, setSearch, page, setPage }) {
  const [famille, setFamille] = useState('toutes');
  /* Le matériel réformé, ainsi que les masques gravés (sans étiquette
     à imprimer), n'ont pas besoin d'étiquette. */
  const unitsActives = useMemo(() => units.filter((u) => !u.reforme && !FAMILLES_SANS_QR.has(u.type)), [units]);
  const familles = useMemo(
    () => Array.from(new Set(unitsActives.map((u) => u.type || 'Autre'))).sort(),
    [unitsActives]
  );

  const matches = (t) => t.toLowerCase().includes(search.toLowerCase());
  const liste = useMemo(() => {
    if (vue === 'materiel') {
      return unitsActives
        .filter((u) => famille === 'toutes' || (u.type || 'Autre') === famille)
        .filter((u) => matches(u.name + ' ' + (u.tag || '')))
        .map((u) => ({ key: u.id, code: codeQR('M', u.id, urlPublique), titre: u.name, sous: u.tag || u.type || 'Matériel' }));
    }
    return refs
      .filter((r) => matches(r.name))
      .map((r) => ({ key: r.id, code: codeQR('C', r.id, urlPublique), titre: r.name, sous: `Consommable · ${r.unit}` }));
  }, [units, refs, vue, famille, search, urlPublique]);

  const pages = Math.max(1, Math.ceil(liste.length / QR_PAR_PAGE));
  const p = Math.min(page, pages - 1);
  const visibles = liste.slice(p * QR_PAR_PAGE, (p + 1) * QR_PAR_PAGE);

  return (
    <section className="px-5 mt-4">
      <p className="text-xs mb-3" style={{ color: C.soft }}>
        Une étiquette par unité de matériel, une par référence de consommable. L'outillage n'en a pas.
        Les étiquettes s'affichent par planches de {QR_PAR_PAGE} : imprimez planche par planche.
      </p>

      <div className="flex gap-2 mb-2">
        {[
          { id: 'materiel', label: `Matériel (${unitsActives.length})`, icon: Wrench },
          { id: 'conso', label: `Consommables (${refs.length})`, icon: Package },
        ].map((t) => {
          const Icon = t.icon, on = vue === t.id;
          return (
            <button key={t.id} onClick={() => setVue(t.id)}
              className="flex-1 rounded-lg py-2 text-xs font-semibold flex items-center justify-center gap-1.5"
              style={{ background: on ? C.steel : C.surface, color: on ? '#fff' : C.soft, border: `1px solid ${on ? C.steel : C.border}` }}>
              <Icon size={14} />{t.label}
            </button>
          );
        })}
      </div>

      <div className="flex items-center gap-2 rounded-lg px-3 py-2 mb-2" style={{ background: C.surface, border: `1px solid ${C.border}` }}>
        <Search size={15} color={C.soft} />
        <input value={search} onChange={(e) => setSearch(e.target.value)}
          placeholder="Rechercher…" className="flex-1 outline-none text-sm bg-transparent" />
        {search && <button onClick={() => setSearch('')} aria-label="Effacer"><X size={15} color={C.soft} /></button>}
      </div>

      {vue === 'materiel' && familles.length > 1 && (
        <select value={famille} onChange={(e) => { setFamille(e.target.value); setPage(0); }}
          className="w-full mb-3 rounded-lg px-3 py-2 text-sm outline-none"
          style={{ background: C.surface, border: `1px solid ${famille === 'toutes' ? C.border : C.accent}`, color: C.ink }}>
          <option value="toutes">Toutes les familles ({units.length})</option>
          {familles.map((f) => (
            <option key={f} value={f}>{f} ({units.filter((u) => (u.type || 'Autre') === f).length})</option>
          ))}
        </select>
      )}

      {liste.length === 0 ? (
        <p className="text-sm text-center py-10" style={{ color: C.soft }}>Aucune étiquette à afficher.</p>
      ) : (
        <>
          <div className="flex items-center justify-between mb-2">
            <span className="text-xs" style={{ color: C.soft }}>
              {p * QR_PAR_PAGE + 1}–{Math.min((p + 1) * QR_PAR_PAGE, liste.length)} sur {liste.length}
            </span>
            <span className="text-xs" style={{ color: C.soft }}>Planche {p + 1} / {pages}</span>
          </div>

          <div className="grid grid-cols-2 gap-3">
            {visibles.map((e) => <Etiquette key={e.key} code={e.code} title={e.titre} sub={e.sous} />)}
          </div>

          {pages > 1 && (
            <div className="flex gap-2 mt-4">
              <button disabled={p === 0} onClick={() => setPage(p - 1)}
                className="flex-1 rounded-lg py-2.5 text-sm font-semibold"
                style={{ background: p === 0 ? C.border : C.surface, color: p === 0 ? C.soft : C.ink, border: `1px solid ${C.border}` }}>
                Planche précédente
              </button>
              <button disabled={p >= pages - 1} onClick={() => setPage(p + 1)}
                className="flex-1 rounded-lg py-2.5 text-sm font-semibold"
                style={{ background: p >= pages - 1 ? C.border : C.accent, color: p >= pages - 1 ? C.soft : C.ink }}>
                Planche suivante
              </button>
            </div>
          )}
        </>
      )}
    </section>
  );
}

/* =================== ALERTES RÉVISIONS =================== */

/* =================== MASQUES ATTRIBUÉS =================== */

function MasquesAttribuesPanel({ masques, canGerer, onAttribuer, onRenouveler, onPerdu, onRenouvelerFitTest }) {
  const [search, setSearch] = useState('');
  const [voirHistorique, setVoirHistorique] = useState(false);
  const [modal, setModal] = useState(null); // 'nouveau' | { type:'renouveler'|'perdu', masque }

  const echeance = (m) => addDays(m.dateMiseEnService || todayISO(), REVISION_JOURS);
  const joursMasque = (m) => daysUntil(echeance(m));
  const echeanceFitTest = (m) => addDays(m.dateFitTest, REVISION_JOURS);
  const joursFitTest = (m) => (m.dateFitTest ? daysUntil(echeanceFitTest(m)) : null);

  const actifs = masques.filter((m) => !m.reforme);
  const historique = masques.filter((m) => m.reforme).sort((a, b) => (b.reformeDate || '').localeCompare(a.reformeDate || ''));

  const filtres = actifs.filter((m) => (m.personne + ' ' + m.numeroMasque + ' ' + m.numeroInterne).toLowerCase().includes(search.toLowerCase()))
    .sort((a, b) => joursMasque(a) - joursMasque(b));

  const enRetard = actifs.filter((m) => joursMasque(m) < 0).length;
  const bientot = actifs.filter((m) => { const j = joursMasque(m); return j >= 0 && j <= ALERTE_JOURS; }).length;
  const avecFitTest = actifs.filter((m) => m.dateFitTest);
  const fitTestRetard = avecFitTest.filter((m) => joursFitTest(m) < 0).length;
  const fitTestBientot = avecFitTest.filter((m) => { const j = joursFitTest(m); return j >= 0 && j <= ALERTE_JOURS; }).length;

  return (
    <section className="px-5 mt-4 pb-8">
      <p className="text-xs mb-3" style={{ color: C.soft }}>
        Masques VA et adduction d'air attribués nominativement. Page indépendante du Parc : un masque attribué
        n'est ni commandé ni scanné — à l'échéance des 365 jours, il est intégralement renouvelé.
      </p>

      {(enRetard > 0 || bientot > 0 || fitTestRetard > 0 || fitTestBientot > 0) && (
        <div className="rounded-lg px-4 py-3 mb-3 text-sm flex flex-col gap-1"
          style={{ background: (enRetard || fitTestRetard) ? C.redSoft : C.amberSoft, color: (enRetard || fitTestRetard) ? C.red : C.amber }}>
          {enRetard > 0 && <span className="flex items-center gap-2"><AlertTriangle size={15} />{enRetard} masque{enRetard > 1 ? 's' : ''} à renouveler sans délai</span>}
          {bientot > 0 && <span className="flex items-center gap-2"><CalendarClock size={15} />{bientot} masque{bientot > 1 ? 's' : ''} à renouveler sous {ALERTE_JOURS} jours</span>}
          {fitTestRetard > 0 && <span className="flex items-center gap-2"><AlertTriangle size={15} />{fitTestRetard} fit test{fitTestRetard > 1 ? 's' : ''} dépassé{fitTestRetard > 1 ? 's' : ''}</span>}
          {fitTestBientot > 0 && <span className="flex items-center gap-2"><CalendarClock size={15} />{fitTestBientot} fit test{fitTestBientot > 1 ? 's' : ''} à renouveler sous {ALERTE_JOURS} jours</span>}
        </div>
      )}

      <div className="flex items-center gap-2 rounded-lg px-3 py-2 mb-4" style={{ background: C.surface, border: `1px solid ${C.border}` }}>
        <Search size={15} color={C.soft} />
        <input value={search} onChange={(e) => setSearch(e.target.value)} placeholder="Rechercher une personne…" className="flex-1 outline-none text-sm bg-transparent" />
      </div>

      {actifs.length === 0 ? (
        <Empty icon={Shield} title="Aucun masque attribué" text="Attribuez un masque à une personne pour commencer le suivi."
          cta={canGerer ? 'Attribuer un masque' : null} onCta={() => setModal('nouveau')} />
      ) : filtres.length === 0 ? (
        <p className="text-sm text-center py-8" style={{ color: C.soft }}>Aucun résultat.</p>
      ) : (
        <div className="flex flex-col gap-2">
          {filtres.map((m) => {
            const j = joursMasque(m);
            const tone = j < 0 ? { c: C.red, s: C.redSoft } : j <= ALERTE_JOURS ? { c: C.amber, s: C.amberSoft } : { c: C.green, s: C.greenSoft };
            const jFit = joursFitTest(m);
            const toneFit = jFit === null ? null : jFit < 0 ? { c: C.red, s: C.redSoft } : jFit <= ALERTE_JOURS ? { c: C.amber, s: C.amberSoft } : { c: C.green, s: C.greenSoft };
            return (
              <div key={m.id} className="rounded-lg px-4 py-3" style={{ background: C.surface, border: `1px solid ${C.border}`, borderLeft: `4px solid ${tone.c}` }}>
                <div className="flex items-start justify-between gap-3">
                  <div className="min-w-0">
                    <p className="text-sm font-semibold truncate">{m.personne}</p>
                    <p className="text-xs" style={{ color: C.soft }}>
                      {m.type} · n° {m.numeroMasque || m.numeroInterne}{m.taille ? ` · taille ${m.taille}` : ''}
                    </p>
                  </div>
                  <span className="text-[11px] font-semibold rounded px-2 py-1 flex-shrink-0" style={{ background: tone.s, color: tone.c }}>
                    Masque {j < 0 ? `+${-j} j` : `J−${j}`}
                  </span>
                </div>
                <p className="text-[11px] mt-1.5" style={{ color: j < 0 ? C.red : C.soft }}>
                  Masque à renouveler avant le {frDate(echeance(m))}
                </p>

                <div className="flex items-center justify-between gap-3 mt-2 pt-2" style={{ borderTop: `1px solid ${C.border}` }}>
                  {m.dateFitTest ? (
                    <>
                      <p className="text-[11px]" style={{ color: jFit < 0 ? C.red : C.soft }}>
                        Fit test à renouveler avant le {frDate(echeanceFitTest(m))}
                      </p>
                      <span className="text-[11px] font-semibold rounded px-2 py-1 flex-shrink-0" style={{ background: toneFit.s, color: toneFit.c }}>
                        {jFit < 0 ? `+${-jFit} j` : `J−${jFit}`}
                      </span>
                    </>
                  ) : (
                    <p className="text-[11px]" style={{ color: C.soft }}>Aucune date de fit test enregistrée.</p>
                  )}
                </div>
                {canGerer && (
                  <button onClick={() => setModal({ type: 'fittest', masque: m })} className="text-xs font-semibold mt-1.5" style={{ color: C.steelMid }}>
                    {m.dateFitTest ? 'Renouveler le fit test' : 'Enregistrer un fit test'}
                  </button>
                )}

                {canGerer && (
                  <div className="flex gap-2 mt-2.5">
                    <button onClick={() => setModal({ type: 'perdu', masque: m })}
                      className="flex-1 rounded-md py-1.5 text-xs font-semibold" style={{ border: `1px solid ${C.border}`, color: C.soft }}>
                      Déclarer perdu
                    </button>
                    <button onClick={() => setModal({ type: 'renouveler', masque: m })}
                      className="flex-1 rounded-md py-1.5 text-xs font-semibold" style={{ background: C.steel, color: '#fff' }}>
                      Renouveler le masque
                    </button>
                  </div>
                )}
              </div>
            );
          })}
        </div>
      )}

      {historique.length > 0 && (
        <>
          <button onClick={() => setVoirHistorique(!voirHistorique)} className="text-xs mt-5 mb-2 flex items-center gap-1" style={{ color: C.soft }}>
            {voirHistorique ? <ChevronUp size={13} /> : <ChevronDown size={13} />}
            Historique ({historique.length})
          </button>
          {voirHistorique && (
            <div className="flex flex-col gap-2">
              {historique.map((m) => (
                <div key={m.id} className="rounded-lg px-4 py-3" style={{ background: C.surface, border: `1px solid ${C.border}`, opacity: 0.75 }}>
                  <p className="text-sm font-medium">{m.personne}</p>
                  <p className="text-xs" style={{ color: C.soft }}>
                    {m.type} · n° {m.numeroMasque || m.numeroInterne} — {m.reformeMotif} le {frDate(m.reformeDate)}
                    {m.reformeComment ? ` — ${m.reformeComment}` : ''}
                  </p>
                </div>
              ))}
            </div>
          )}
        </>
      )}

      {canGerer && (
        <button onClick={() => setModal('nouveau')}
          className="fixed bottom-6 right-6 rounded-full flex items-center justify-center shadow-lg z-30"
          style={{ width: 54, height: 54, background: C.accent }} aria-label="Attribuer un masque">
          <Plus size={24} color={C.ink} />
        </button>
      )}

      {modal === 'nouveau' && (
        <MasqueForm titre="Attribuer un masque" onClose={() => setModal(null)}
          onSave={(d) => { onAttribuer(d); setModal(null); }} />
      )}
      {modal && modal.type === 'renouveler' && (
        <MasqueForm titre={`Renouveler — ${modal.masque.personne}`} personneFixe={modal.masque.personne} typeFixe={modal.masque.type}
          onClose={() => setModal(null)}
          onSave={(d) => { onRenouveler(modal.masque, d); setModal(null); }} />
      )}
      {modal && modal.type === 'perdu' && (
        <PerduSheet masque={modal.masque} onClose={() => setModal(null)}
          onSave={(commentaire) => { onPerdu(modal.masque, commentaire); setModal(null); }} />
      )}
      {modal && modal.type === 'fittest' && (
        <FitTestSheet masque={modal.masque} onClose={() => setModal(null)}
          onSave={(date) => { onRenouvelerFitTest(modal.masque, date); setModal(null); }} />
      )}
    </section>
  );
}

function FitTestSheet({ masque, onClose, onSave }) {
  const [date, setDate] = useState(todayISO());
  return (
    <Sheet title={`Fit test — ${masque.personne}`} onClose={onClose}>
      <p className="text-xs mb-3" style={{ color: C.soft }}>
        Nouvelle date de passage du fit test pour le masque {masque.type} n° {masque.numeroMasque || masque.numeroInterne}.
      </p>
      <Field label="Date du fit test">
        <DatePicker value={date} onChange={setDate} />
      </Field>
      <p className="text-xs mb-3" style={{ color: C.soft }}>
        Prochaine échéance : {frDate(addDays(date || todayISO(), REVISION_JOURS))}.
      </p>
      <PrimaryButton onClick={() => onSave(date)}>Enregistrer le fit test</PrimaryButton>
    </Sheet>
  );
}

function MasqueForm({ titre, personneFixe, typeFixe, onClose, onSave }) {
  const [personne, setPersonne] = useState(personneFixe || '');
  const [type, setType] = useState(typeFixe || 'VA');
  const [numeroInterne, setNumeroInterne] = useState('');
  const [numeroMasque, setNumeroMasque] = useState('');
  const [taille, setTaille] = useState('');
  const [dateMiseEnService, setDateMiseEnService] = useState(todayISO());
  const [dateFitTest, setDateFitTest] = useState('');

  const pret = personne.trim() && (numeroInterne.trim() || numeroMasque.trim()) && dateMiseEnService;

  return (
    <Sheet title={titre} onClose={onClose}>
      <Field label="Personne">
        <input style={inputStyle} value={personne} onChange={(e) => setPersonne(e.target.value)} placeholder="Nom Prénom" disabled={!!personneFixe} />
      </Field>
      <Field label="Type de masque">
        <div className="flex gap-2">
          {['VA', 'AA'].map((t) => (
            <button key={t} type="button" onClick={() => !typeFixe && setType(t)}
              className="flex-1 rounded-lg py-2 text-sm font-semibold" disabled={!!typeFixe}
              style={{ background: type === t ? C.steel : '#FCFBF9', color: type === t ? '#fff' : C.soft, border: `1px solid ${type === t ? C.steel : C.border}` }}>
              {t === 'VA' ? 'Ventilation assistée' : "Adduction d'air"}
            </button>
          ))}
        </div>
      </Field>
      <div className="grid grid-cols-2 gap-3">
        <Field label="N° interne">
          <input style={inputStyle} value={numeroInterne} onChange={(e) => setNumeroInterne(e.target.value)} placeholder="Ex. 110" />
        </Field>
        <Field label="Taille">
          <input style={inputStyle} value={taille} onChange={(e) => setTaille(e.target.value)} placeholder="S / M / L" />
        </Field>
      </div>
      <Field label="N° de masque / série">
        <input style={inputStyle} value={numeroMasque} onChange={(e) => setNumeroMasque(e.target.value)} placeholder="Ex. 230610050090034L" />
      </Field>
      <Field label="Date de mise en service">
        <DatePicker value={dateMiseEnService} onChange={setDateMiseEnService} />
      </Field>
      <p className="text-xs mb-3" style={{ color: C.soft }}>
        À renouveler avant le {frDate(addDays(dateMiseEnService || todayISO(), REVISION_JOURS))}.
      </p>
      <Field label="Date du FIT TEST (optionnel)">
        <DatePicker value={dateFitTest} onChange={setDateFitTest} />
      </Field>
      <PrimaryButton disabled={!pret} onClick={() => onSave({ personne: personne.trim(), type, numeroInterne: numeroInterne.trim(), numeroMasque: numeroMasque.trim(), taille: taille.trim(), dateMiseEnService, dateFitTest })}>
        Enregistrer
      </PrimaryButton>
    </Sheet>
  );
}

function PerduSheet({ masque, onClose, onSave }) {
  const [commentaire, setCommentaire] = useState('');
  return (
    <Sheet title={`Déclarer perdu — ${masque.personne}`} onClose={onClose}>
      <p className="text-xs mb-3" style={{ color: C.soft }}>
        Le masque {masque.type} n° {masque.numeroMasque || masque.numeroInterne} sera archivé comme perdu.
        Pensez à attribuer un nouveau masque à {masque.personne} si nécessaire.
      </p>
      <Field label="Commentaire (optionnel)">
        <input style={inputStyle} value={commentaire} onChange={(e) => setCommentaire(e.target.value)} placeholder="Ex. perdu sur le chantier de…" />
      </Field>
      <PrimaryButton color={C.red} onClick={() => onSave(commentaire.trim())}>Confirmer la perte</PrimaryButton>
    </Sheet>
  );
}

function AlertesPanel({ units, masques, emails, users, isAdmin, onAdd, onRemove, onSent }) {
  const [mail, setMail] = useState('');
  const valide = /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(mail.trim());

  const emailsUtilisateurs = (users || [])
    .filter((u) => u.email && !emails.includes(u.email.trim().toLowerCase()))
    .sort((a, b) => a.name.localeCompare(b.name));

  const depasses = units.filter((u) => daysUntil(prochaineRevision(u)) < 0);
  const aVenir = units.filter((u) => daysUntil(prochaineRevision(u)) >= 0);

  const echeanceMasque = (m) => addDays(m.dateMiseEnService || todayISO(), REVISION_JOURS);
  const echeanceFitTest = (m) => addDays(m.dateFitTest, REVISION_JOURS);
  const masqueEnRetard = (m) => daysUntil(echeanceMasque(m)) < 0;
  const fitTestConcerne = (m) => m.dateFitTest && daysUntil(echeanceFitTest(m)) <= ALERTE_JOURS;
  const fitTestEnRetard = (m) => m.dateFitTest && daysUntil(echeanceFitTest(m)) < 0;

  const masquesDepasses = masques.filter((m) => masqueEnRetard(m));
  const masquesAVenir = masques.filter((m) => !masqueEnRetard(m) && daysUntil(echeanceMasque(m)) <= ALERTE_JOURS);
  const fitTestDepasses = masques.filter((m) => fitTestEnRetard(m));
  const fitTestAVenir = masques.filter((m) => fitTestConcerne(m) && !fitTestEnRetard(m));

  const total = units.length + masques.length;

  function corps() {
    const lignes = [];
    lignes.push(`Point revisions materiel et masques - APII - ${new Date().toLocaleDateString('fr-FR')}`);
    lignes.push('');
    if (depasses.length) {
      lignes.push(`REVISION MATERIEL DEPASSEE - ${depasses.length} materiel(s) en quarantaine, non utilisables :`);
      depasses.forEach((u) => {
        const j = daysUntil(prochaineRevision(u));
        lignes.push(`- ${u.name}${u.tag ? ` (${u.tag})` : ''} : echeance du ${frDate(prochaineRevision(u))}, depassee de ${-j} jours`);
      });
      lignes.push('');
    }
    if (aVenir.length) {
      lignes.push(`MATERIEL A PLANIFIER SOUS ${ALERTE_JOURS} JOURS - ${aVenir.length} materiel(s) :`);
      aVenir.forEach((u) => {
        const j = daysUntil(prochaineRevision(u));
        lignes.push(`- ${u.name}${u.tag ? ` (${u.tag})` : ''} : a reviser avant le ${frDate(prochaineRevision(u))} (J-${j})`);
      });
      lignes.push('');
    }
    if (masquesDepasses.length) {
      lignes.push(`RENOUVELLEMENT MASQUE DEPASSE - ${masquesDepasses.length} masque(s) attribue(s) :`);
      masquesDepasses.forEach((m) => {
        const j = daysUntil(echeanceMasque(m));
        lignes.push(`- ${m.personne} - masque ${m.type} n° ${m.numeroMasque || m.numeroInterne} : echeance du ${frDate(echeanceMasque(m))}, depassee de ${-j} jours`);
      });
      lignes.push('');
    }
    if (masquesAVenir.length) {
      lignes.push(`MASQUES A RENOUVELER SOUS ${ALERTE_JOURS} JOURS - ${masquesAVenir.length} masque(s) :`);
      masquesAVenir.forEach((m) => {
        const j = daysUntil(echeanceMasque(m));
        lignes.push(`- ${m.personne} - masque ${m.type} n° ${m.numeroMasque || m.numeroInterne} : a renouveler avant le ${frDate(echeanceMasque(m))} (J-${j})`);
      });
      lignes.push('');
    }
    if (fitTestDepasses.length) {
      lignes.push(`FIT TEST DEPASSE - ${fitTestDepasses.length} personne(s) :`);
      fitTestDepasses.forEach((m) => {
        const j = daysUntil(echeanceFitTest(m));
        lignes.push(`- ${m.personne} - masque ${m.type} : fit test echeance du ${frDate(echeanceFitTest(m))}, depasse de ${-j} jours`);
      });
      lignes.push('');
    }
    if (fitTestAVenir.length) {
      lignes.push(`FIT TEST A RENOUVELER SOUS ${ALERTE_JOURS} JOURS - ${fitTestAVenir.length} personne(s) :`);
      fitTestAVenir.forEach((m) => {
        const j = daysUntil(echeanceFitTest(m));
        lignes.push(`- ${m.personne} - masque ${m.type} : fit test a renouveler avant le ${frDate(echeanceFitTest(m))} (J-${j})`);
      });
      lignes.push('');
    }
    lignes.push('Un materiel dont la revision est depassee bascule automatiquement en quarantaine et ne peut plus etre charge.');
    lignes.push('Un masque attribue non renouvele a echeance doit etre remplace au plus vite.');
    return lignes.join('\n');
  }

  const mailto = `mailto:${emails.join(',')}?subject=${encodeURIComponent(`[APII] Révisions et masques — ${total} à traiter`)}&body=${encodeURIComponent(corps())}`;

  return (
    <section className="px-5 mt-4">
      <div className="rounded-lg px-4 py-3 mb-4 text-sm"
        style={{ background: (depasses.length || masquesDepasses.length) ? C.redSoft : total ? C.amberSoft : C.greenSoft,
                 color: (depasses.length || masquesDepasses.length) ? C.red : total ? C.amber : C.green }}>
        {total === 0
          ? `Aucune révision ni renouvellement à prévoir dans les ${ALERTE_JOURS} prochains jours.`
          : `${units.length} matériel${units.length > 1 ? 's' : ''} à réviser et ${masques.length} masque${masques.length > 1 ? 's' : ''} à renouveler sous ${ALERTE_JOURS} jours${(depasses.length || masquesDepasses.length) ? `, dont ${depasses.length + masquesDepasses.length} déjà dépassés` : ''}.`}
      </div>

      <SectionTitle icon={Mail} label={`Destinataires (${emails.length})`} />
      <div className="flex flex-col gap-2 mb-3">
        {emails.length === 0 && <p className="text-xs" style={{ color: C.soft }}>Aucun destinataire enregistré.</p>}
        {emails.map((m) => (
          <div key={m} className="rounded-lg px-4 py-2.5 flex items-center justify-between gap-3"
            style={{ background: C.surface, border: `1px solid ${C.border}` }}>
            <span className="text-sm truncate">{m}</span>
            {isAdmin && (
              <button onClick={() => onRemove(m)} aria-label={`Retirer ${m}`}><X size={16} color={C.soft} /></button>
            )}
          </div>
        ))}
      </div>

      {isAdmin && emailsUtilisateurs.length > 0 && (
        <div className="flex flex-col gap-2 mb-3">
          <p className="text-xs" style={{ color: C.soft }}>Depuis les profils utilisateurs :</p>
          {emailsUtilisateurs.map((u) => (
            <button key={u.id} onClick={() => onAdd(u.email.trim().toLowerCase())}
              className="rounded-lg px-4 py-2.5 flex items-center justify-between gap-3 text-left"
              style={{ background: C.surface, border: `1px solid ${C.border}` }}>
              <span className="min-w-0">
                <span className="text-sm font-medium truncate block">{u.name}</span>
                <span className="text-xs truncate block" style={{ color: C.soft }}>{u.email}</span>
              </span>
              <Plus size={16} color={C.soft} className="flex-shrink-0" />
            </button>
          ))}
        </div>
      )}

      {isAdmin ? (
        <div className="flex gap-2 mb-6">
          <input style={inputStyle} type="email" value={mail} onChange={(e) => setMail(e.target.value)} placeholder="prenom.nom@apii.fr" />
          <button onClick={() => { onAdd(mail.trim().toLowerCase()); setMail(''); }} disabled={!valide}
            className="rounded-lg px-4 text-sm font-semibold flex-shrink-0"
            style={{ background: valide ? C.steel : C.border, color: valide ? '#fff' : C.soft }}>
            Ajouter
          </button>
        </div>
      ) : (
        <p className="text-xs mb-6" style={{ color: C.soft }}>Seul l'administrateur modifie la liste des destinataires.</p>
      )}

      {units.length > 0 && (
        <>
          <SectionTitle icon={CalendarClock} label="Matériel concerné" />
          <div className="flex flex-col gap-2 mb-5">
            {units.map((u) => {
              const j = daysUntil(prochaineRevision(u));
              const tone = j < 0 ? { c: C.red, s: C.redSoft } : { c: C.amber, s: C.amberSoft };
              return (
                <div key={u.id} className="rounded-lg px-4 py-3 flex items-center justify-between gap-3"
                  style={{ background: C.surface, border: `1px solid ${C.border}`, borderLeft: `4px solid ${tone.c}` }}>
                  <div className="min-w-0">
                    <p className="text-sm font-medium truncate">{u.name}{u.tag ? ` · ${u.tag}` : ''}</p>
                    <p className="text-xs" style={{ color: C.soft }}>Échéance {frDate(prochaineRevision(u))}</p>
                  </div>
                  <span className="text-[11px] font-semibold rounded px-2 py-1 flex-shrink-0" style={{ background: tone.s, color: tone.c }}>
                    {j < 0 ? `+${-j} j` : `J−${j}`}
                  </span>
                </div>
              );
            })}
          </div>
        </>
      )}

      {masques.length > 0 && (
        <>
          <SectionTitle icon={Shield} label="Masques attribués concernés" />
          <div className="flex flex-col gap-2 mb-5">
            {masques.map((m) => {
              const concerneParMasque = daysUntil(echeanceMasque(m)) <= ALERTE_JOURS;
              const concerneParFitTest = fitTestConcerne(m);
              const j = daysUntil(echeanceMasque(m));
              const jFit = m.dateFitTest ? daysUntil(echeanceFitTest(m)) : null;
              const pire = Math.min(j, jFit !== null ? jFit : Infinity);
              const tone = pire < 0 ? { c: C.red, s: C.redSoft } : { c: C.amber, s: C.amberSoft };
              return (
                <div key={m.id} className="rounded-lg px-4 py-3" style={{ background: C.surface, border: `1px solid ${C.border}`, borderLeft: `4px solid ${tone.c}` }}>
                  <p className="text-sm font-medium truncate">{m.personne} · {m.type}</p>
                  <p className="text-xs" style={{ color: C.soft }}>n° {m.numeroMasque || m.numeroInterne}</p>
                  {concerneParMasque && (
                    <p className="text-xs mt-1" style={{ color: j < 0 ? C.red : C.amber }}>
                      Masque à renouveler avant le {frDate(echeanceMasque(m))} ({j < 0 ? `+${-j} j` : `J−${j}`})
                    </p>
                  )}
                  {concerneParFitTest && (
                    <p className="text-xs mt-1" style={{ color: jFit < 0 ? C.red : C.amber }}>
                      Fit test à renouveler avant le {frDate(echeanceFitTest(m))} ({jFit < 0 ? `+${-jFit} j` : `J−${jFit}`})
                    </p>
                  )}
                </div>
              );
            })}
          </div>
        </>
      )}

      {total > 0 && (
        <>
          <a href={emails.length ? mailto : undefined}
            onClick={() => emails.length && onSent(total)}
            className="block w-full rounded-lg py-2.5 text-sm font-semibold text-center"
            style={{ background: emails.length ? C.accent : C.border, color: emails.length ? C.ink : C.soft, pointerEvents: emails.length ? 'auto' : 'none' }}>
            <span className="flex items-center justify-center gap-2"><Send size={16} /> Préparer l'e-mail d'alerte</span>
          </a>
          <p className="text-[11px] text-center mt-2 mb-2" style={{ color: C.soft }}>
            Ouvre votre messagerie avec le récapitulatif déjà rédigé. L'envoi automatique demanderait un serveur.
          </p>
        </>
      )}
    </section>
  );
}

/* =================== COMPOSANTS =================== *//* =================== COMPOSANTS =================== */

function CommandeCarte({ c, onOpen }) {
  const st = STATUTS[c.statut];
  const nbC = c.consos.reduce((a, l) => a + l.qty, 0);
  return (
    <button onClick={onOpen} className="text-left rounded-lg px-4 py-3"
      style={{ background: C.surface, border: `1px solid ${C.border}` }}>
      <div className="flex items-center justify-between gap-2">
        <div className="flex items-center gap-1.5 min-w-0">
          <span className="text-sm font-bold">{c.num}</span>
          {c.type === 'appoint' && (
            <span className="text-[10px] font-semibold rounded px-1.5 py-0.5" style={{ background: C.greenSoft, color: C.green }}>APPOINT</span>
          )}
        </div>
        <span className="text-[11px] font-semibold rounded px-2 py-0.5" style={{ background: st.soft, color: st.color }}>{st.label}</span>
      </div>
      <p className="text-sm mt-1">{c.chantier}</p>
      <p className="text-xs mt-0.5" style={{ color: C.soft }}>
        {c.unitIds.length} matériel · {nbC} consommable{nbC > 1 ? 's' : ''} · {c.demandeur}
      </p>
      {c.dateLivraison && (
        <p className="text-xs mt-0.5 flex items-center gap-1"
          style={{ color: c.statut === 'a_preparer' && c.dateLivraison < todayISO() ? C.red : C.soft }}>
          <CalendarClock size={11} /> Livraison {frDate(c.dateLivraison)}
        </p>
      )}
    </button>
  );
}

function SectionTitle({ icon: Icon, label }) {
  return (
    <div className="flex items-center gap-1.5 mb-2">
      <Icon size={14} color={C.soft} />
      <h2 className="text-sm font-semibold" style={{ color: C.soft }}>{label}</h2>
    </div>
  );
}

function Empty({ icon: Icon, title, text, cta, onCta }) {
  return (
    <div className="flex flex-col items-center text-center py-14 gap-3">
      <div className="rounded-full flex items-center justify-center" style={{ width: 54, height: 54, background: C.steelSoft }}>
        <Icon size={23} color={C.steel} />
      </div>
      <p className="text-sm font-semibold">{title}</p>
      <p className="text-xs max-w-[250px]" style={{ color: C.soft }}>{text}</p>
      {cta && <button onClick={onCta} className="mt-1 rounded-lg px-4 py-2 text-sm font-semibold" style={{ background: C.accent, color: C.ink }}>{cta}</button>}
    </div>
  );
}

function Etiquette({ code, title, sub }) {
  return (
    <div className="rounded-lg p-3 flex flex-col items-center text-center" style={{ background: C.surface, border: `1px solid ${C.border}` }}>
      <QrSvg text={code} size={104} />
      <p className="text-xs font-semibold mt-2 leading-tight">{title}</p>
      <p className="text-[10px]" style={{ color: C.soft }}>{sub}</p>
    </div>
  );
}

function Sheet({ title, onClose, children }) {
  return (
    <div className="fixed inset-0 z-40 flex items-end sm:items-center justify-center" style={{ background: 'rgba(27,26,24,0.5)' }} onClick={onClose}>
      <div onClick={(e) => e.stopPropagation()}
        className="w-full sm:max-w-sm rounded-t-2xl sm:rounded-2xl px-5 pt-5 pb-6 max-h-[86vh] overflow-y-auto"
        style={{ background: C.surface }}>
        <div className="flex items-center justify-between mb-4">
          <h3 className="text-base font-bold pr-4">{title}</h3>
          <button onClick={onClose} aria-label="Fermer"><X size={20} color={C.soft} /></button>
        </div>
        {children}
      </div>
    </div>
  );
}

const inputStyle = {
  width: '100%', borderRadius: 8, border: `1px solid ${C.border}`,
  padding: '9px 10px', fontSize: 14, outline: 'none', color: C.ink, background: '#FCFBF9',
};

function Field({ label, children }) {
  return (
    <div className="mb-3">
      <label className="text-xs font-medium block mb-1" style={{ color: C.soft }}>{label}</label>
      {children}
    </div>
  );
}

/* Calendrier déroulant fait maison — remplace les champs date natifs du
   navigateur, dont l'apparence varie d'un appareil à l'autre. S'ouvre en
   ligne sous le champ, comme les autres confirmations de l'application. */
const MOIS_NOMS = ['janvier','février','mars','avril','mai','juin','juillet','août','septembre','octobre','novembre','décembre'];
const JOURS_COURTS = ['L','M','M','J','V','S','D'];

function toISO(d) {
  return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`;
}

function DatePicker({ value, onChange, min }) {
  const [ouvert, setOuvert] = useState(false);
  const depart = value ? new Date(value + 'T12:00:00') : (min ? new Date(min + 'T12:00:00') : new Date());
  const [moisAffiche, setMoisAffiche] = useState(new Date(depart.getFullYear(), depart.getMonth(), 1));
  const aujourdhui = toISO(new Date());

  const cases = useMemo(() => {
    const annee = moisAffiche.getFullYear(), mois = moisAffiche.getMonth();
    const premierJour = new Date(annee, mois, 1);
    const dernierJour = new Date(annee, mois + 1, 0);
    const decalage = (premierJour.getDay() + 6) % 7; // la semaine commence le lundi
    const out = [];
    for (let i = 0; i < decalage; i++) out.push(null);
    for (let j = 1; j <= dernierJour.getDate(); j++) out.push(new Date(annee, mois, j));
    return out;
  }, [moisAffiche]);

  return (
    <div>
      <button type="button" onClick={() => setOuvert(!ouvert)}
        className="w-full flex items-center justify-between rounded-lg px-3 py-2 text-sm"
        style={{ border: `1px solid ${C.border}`, background: '#FCFBF9', color: value ? C.ink : C.soft }}>
        <span>{value ? frDate(value) : 'Choisir une date'}</span>
        <CalendarClock size={15} color={C.soft} />
      </button>

      {ouvert && (
        <div className="mt-2 rounded-lg p-3" style={{ border: `1px solid ${C.border}`, background: C.surface }}>
          <div className="flex items-center justify-between mb-2">
            <button type="button" onClick={() => setMoisAffiche(new Date(moisAffiche.getFullYear(), moisAffiche.getMonth() - 1, 1))}
              className="rounded-md p-1" style={{ background: C.steelSoft }} aria-label="Mois précédent">
              <ChevronLeft size={15} color={C.steel} />
            </button>
            <span className="text-sm font-semibold">{MOIS_NOMS[moisAffiche.getMonth()]} {moisAffiche.getFullYear()}</span>
            <button type="button" onClick={() => setMoisAffiche(new Date(moisAffiche.getFullYear(), moisAffiche.getMonth() + 1, 1))}
              className="rounded-md p-1" style={{ background: C.steelSoft }} aria-label="Mois suivant">
              <ChevronRight size={15} color={C.steel} />
            </button>
          </div>

          <div className="grid grid-cols-7 gap-1 mb-1">
            {JOURS_COURTS.map((j, i) => (
              <div key={i} className="text-center text-[10px] font-semibold" style={{ color: C.soft }}>{j}</div>
            ))}
          </div>

          <div className="grid grid-cols-7 gap-1">
            {cases.map((d, i) => {
              if (!d) return <div key={i} />;
              const iso = toISO(d);
              const desactive = !!min && iso < min;
              const selectionne = iso === value;
              const estAujourdhui = iso === aujourdhui;
              return (
                <button key={i} type="button" disabled={desactive}
                  onClick={() => { onChange(iso); setOuvert(false); }}
                  className="rounded-md py-1.5 text-xs"
                  style={{
                    background: selectionne ? C.accent : 'transparent',
                    color: desactive ? C.border : C.ink,
                    fontWeight: selectionne || estAujourdhui ? 700 : 400,
                    border: estAujourdhui && !selectionne ? `1.5px solid ${C.accent}` : '1.5px solid transparent',
                  }}>
                  {d.getDate()}
                </button>
              );
            })}
          </div>

          <button type="button" onClick={() => { onChange(aujourdhui); setOuvert(false); }}
            className="w-full mt-2 text-xs font-semibold py-1.5 rounded-md" style={{ color: C.steelMid, background: C.steelSoft }}>
            Aujourd'hui
          </button>
        </div>
      )}
    </div>
  );
}

function PrimaryButton({ children, disabled, onClick, color = C.accent }) {
  return (
    <button onClick={onClick} disabled={disabled} className="w-full rounded-lg py-2.5 text-sm font-semibold"
      style={{ background: disabled ? C.border : color, color: disabled ? C.soft : onColor(color) }}>
      {children}
    </button>
  );
}

/* =================== FICHE MATÉRIEL =================== */

function UnitSheet({ unit: u, journal, commandes, canRevise, canEtat, urlPublique, onClose, onRevise, onReformer, onAnnulerReforme, onChangerEtat, onModifierLiens }) {
  const [note, setNote] = useState('');
  const [facture, setFacture] = useState('');
  const [confirm, setConfirm] = useState(false);
  const [confirmReforme, setConfirmReforme] = useState(false);
  const [motifReforme, setMotifReforme] = useState('');
  const [modifierEtat, setModifierEtat] = useState(false);
  const [editLiens, setEditLiens] = useState(false);
  const [lienNotice, setLienNotice] = useState(u ? u.lienNotice || '' : '');
  const [lienFiche, setLienFiche] = useState(u ? u.lienFicheRevision || '' : '');
  const [exportEnCours, setExportEnCours] = useState(false);
  if (!u) return null;
  const e = etatUnite(u);
  const etat = ETATS[u.etat];
  const EtatIcon = etat.icon;
  const estMasque = FAMILLES_MASQUE.has(u.type);
  /* L'historique se déduit des commandes : chaque chargement est un départ,
     chaque repli un retour, avec l'état constaté. */
  const passages = (commandes || [])
    .filter((c) => c.charge && c.charge.unitIds.includes(u.id))
    .map((c) => ({
      num: c.num, chantier: c.chantier,
      depart: c.chargeAt ? c.chargeAt.slice(0, 10) : null,
      retour: c.repliAt ? c.repliAt.slice(0, 10) : null,
      etat: c.repli && c.repli.units[u.id] ? c.repli.units[u.id].etat : null,
      commentaire: c.repli && c.repli.units[u.id] ? c.repli.units[u.id].comment : '',
    }))
    .sort((a, b) => (b.depart || '').localeCompare(a.depart || ''));
  /* Comparaison au libellé exact (nom + n° de série), pas seulement au nom :
     plusieurs unités importées partagent la même désignation (jusqu'à 12 pour
     un même modèle) — un simple "includes" mélangerait leurs historiques. */
  const libelleUnite = u.name + (u.tag ? ` · ${u.tag}` : '');
  const historiqueMaintenance = journal
    .filter((j) => ['revision', 'reforme', 'etat'].includes(j.type) && j.label === libelleUnite)
    .sort((a, b) => a.date.localeCompare(b.date));
  const revisions = historiqueMaintenance.filter((j) => j.type === 'revision').slice(-3).reverse();

  return (
    <Sheet title={u.name} onClose={onClose}>
      <div className="flex items-center gap-2 mb-2 flex-wrap">
        <span className="text-[11px] font-semibold rounded px-2 py-1" style={{ background: e.soft, color: e.color }}>{e.label}</span>
        <span className="text-[11px] font-semibold rounded px-2 py-1 flex items-center gap-1" style={{ background: etat.soft, color: etat.color }}>
          <EtatIcon size={12} />{etat.label}
        </span>
      </div>

      {canEtat && !u.reforme && !estMasque && (
        <button onClick={() => setModifierEtat(true)} className="text-xs font-semibold mb-4" style={{ color: C.steelMid }}>
          Modifier l'état
        </button>
      )}
      {!canEtat && <div className="mb-4" />}

      <dl className="text-sm flex flex-col gap-2 mb-4">
        <Row k="Famille" v={u.type || '—'} />
        <Row k="N° de série" v={u.tag || '—'} />
        <Row k="Emplacement" v={u.lieu} />
        <Row k="Dernière révision" v={frDate(u.dateRevision)} />
        {u.derniereFacture && <Row k="N° de facture" v={u.derniereFacture} />}
        <Row k="Prochaine révision" v={frDate(e.next)} tone={e.j < 0 ? C.red : e.j <= ALERTE_JOURS ? C.amber : undefined} />
        <Row k="Échéance" v={e.j < 0 ? `dépassée de ${-e.j} j` : `dans ${e.j} j`} tone={e.j < 0 ? C.red : undefined} />
      </dl>

      {/* Documents liés : simples liens externes, l'application ne stocke pas de fichiers PDF. */}
      <div className="mb-4">
        {(u.lienNotice || u.lienFicheRevision) && (
          <div className="flex flex-col gap-1.5 mb-2">
            {u.lienNotice && (
              <a href={u.lienNotice} target="_blank" rel="noopener noreferrer"
                className="text-xs font-semibold flex items-center gap-1.5" style={{ color: C.steelMid }}>
                <Link2 size={13} /> Notice d'utilisation
              </a>
            )}
            {u.lienFicheRevision && (
              <a href={u.lienFicheRevision} target="_blank" rel="noopener noreferrer"
                className="text-xs font-semibold flex items-center gap-1.5" style={{ color: C.steelMid }}>
                <Link2 size={13} /> Fiche de révision
              </a>
            )}
          </div>
        )}
        {canRevise && (
          editLiens ? (
            <div className="rounded-lg px-3 py-3" style={{ border: `1px dashed ${C.border}` }}>
              <Field label="Lien vers la notice d'utilisation">
                <input style={inputStyle} value={lienNotice} onChange={(e2) => setLienNotice(e2.target.value)} placeholder="https://…" />
              </Field>
              <Field label="Lien vers la fiche de révision">
                <input style={inputStyle} value={lienFiche} onChange={(e2) => setLienFiche(e2.target.value)} placeholder="https://…" />
              </Field>
              <div className="flex gap-2">
                <button onClick={() => { setEditLiens(false); setLienNotice(u.lienNotice || ''); setLienFiche(u.lienFicheRevision || ''); }}
                  className="flex-1 rounded-lg py-2 text-sm font-semibold" style={{ background: C.steelSoft, color: C.soft }}>
                  Annuler
                </button>
                <button onClick={() => { onModifierLiens(u, lienNotice.trim(), lienFiche.trim()); setEditLiens(false); }}
                  className="flex-1 rounded-lg py-2 text-sm font-semibold" style={{ background: C.steel, color: '#fff' }}>
                  Enregistrer
                </button>
              </div>
            </div>
          ) : (
            <button onClick={() => setEditLiens(true)} className="text-xs font-semibold flex items-center gap-1.5" style={{ color: C.soft }}>
              <Link2 size={13} /> {u.lienNotice || u.lienFicheRevision ? 'Modifier les liens' : 'Ajouter des liens (notice, fiche de révision)'}
            </button>
          )
        )}
      </div>

      <button
        onClick={() => { setExportEnCours(true); setTimeout(() => { try { genererPdfMateriel(u, journal, commandes, urlPublique); } finally { setExportEnCours(false); } }, 30); }}
        disabled={exportEnCours}
        className="w-full mb-4 rounded-lg py-2.5 text-sm font-semibold flex items-center justify-center gap-2"
        style={{ border: `1px solid ${C.border}`, background: C.surface, color: C.ink }}>
        {exportEnCours ? <Loader2 className="animate-spin" size={15} /> : <FileDown size={16} />}
        {exportEnCours ? 'Génération du PDF…' : 'Extraire une fiche PDF'}
      </button>

      {u.comment && (
        <div className="rounded-lg px-3 py-2 mb-4 text-xs" style={{ background: C.redSoft, color: C.red }}>{u.comment}</div>
      )}

      <SectionTitle icon={History} label={`Historique d'utilisation (${passages.length})`} />
      <div className="flex flex-col gap-1.5 mb-4">
        {passages.length === 0 && (
          <p className="text-xs" style={{ color: C.soft }}>Cette unité n'est encore jamais partie en chantier.</p>
        )}
        {passages.map((p) => {
          const e = p.etat ? ETATS[p.etat] : null;
          return (
            <div key={p.num} className="rounded-md px-3 py-2"
              style={{ background: '#FCFBF9', border: `1px solid ${C.border}`, borderLeft: `3px solid ${p.retour ? (e ? e.color : C.border) : C.accent}` }}>
              <div className="flex items-center justify-between gap-2">
                <p className="text-xs font-semibold truncate">{p.chantier}</p>
                <span className="text-[10px] flex-shrink-0" style={{ color: C.soft }}>{p.num}</span>
              </div>
              <p className="text-[11px] mt-0.5" style={{ color: C.soft }}>
                Parti le {frDate(p.depart)}
                {p.retour ? ` · rentré le ${frDate(p.retour)}` : ' · toujours sur chantier'}
              </p>
              {e && (
                <p className="text-[11px] mt-0.5" style={{ color: e.color }}>
                  Retour {e.label.toLowerCase()}{p.commentaire ? ` — ${p.commentaire}` : ''}
                </p>
              )}
            </div>
          );
        })}
      </div>

      {revisions.length > 0 && (
        <>
          <SectionTitle icon={CalendarClock} label="Révisions enregistrées" />
          <div className="flex flex-col gap-1.5 mb-4">
            {revisions.map((j) => (
              <div key={j.id} className="text-xs rounded-md px-3 py-2" style={{ background: '#FCFBF9', border: `1px solid ${C.border}` }}>
                <p>{j.detail}</p>
                <p className="text-[11px] mt-0.5" style={{ color: C.soft }}>{relTime(j.date)} · {j.par}</p>
              </div>
            ))}
          </div>
        </>
      )}

      {u.reforme ? (
        <>
          <div className="rounded-lg px-4 py-3 mb-4" style={{ background: C.steelSoft }}>
            <p className="text-sm font-semibold flex items-center gap-1.5" style={{ color: C.steel }}>
              <Archive size={14} /> Réformé le {frDate(u.reformeDate)}
            </p>
            {u.reformeComment && <p className="text-xs mt-1" style={{ color: C.soft }}>{u.reformeComment}</p>}
          </div>
          {canEtat ? (
            <PrimaryButton color={C.steel} onClick={() => onAnnulerReforme(u)}>
              <span className="flex items-center justify-center gap-2"><RotateCcw size={16} /> Annuler la réforme</span>
            </PrimaryButton>
          ) : (
            <p className="text-xs text-center" style={{ color: C.soft }}>
              Ce matériel est réformé. Seuls le chargé d'affaires ou l'administrateur peuvent annuler la réforme.
            </p>
          )}
        </>
      ) : (
        <>
          {estMasque ? (
            <p className="text-xs mb-3" style={{ color: C.soft }}>
              Un masque ne se révise pas : passé 365 jours, il est directement réformé et remplacé.
            </p>
          ) : canRevise ? (
            confirm ? (
              <>
                <Field label="Compte rendu de révision (optionnel)">
                  <input style={inputStyle} value={note} onChange={(e2) => setNote(e2.target.value)} placeholder="Ex. filtre HEPA remplacé, test d'étanchéité OK" />
                </Field>
                <Field label="N° de facture (optionnel)">
                  <input style={inputStyle} value={facture} onChange={(e2) => setFacture(e2.target.value)} placeholder="Ex. FA-2026-0342" />
                </Field>
                <p className="text-xs mb-3" style={{ color: C.soft }}>
                  La révision remet le matériel en service au dépôt, état propre, pour {REVISION_JOURS} jours.
                </p>
                <PrimaryButton color={C.green} onClick={() => onRevise(u, note.trim(), facture.trim())}>Confirmer la révision</PrimaryButton>
              </>
            ) : (
              <PrimaryButton color={C.steel} onClick={() => setConfirm(true)}>
                <span className="flex items-center justify-center gap-2"><CalendarClock size={16} /> Enregistrer une révision</span>
              </PrimaryButton>
            )
          ) : (
            <p className="text-xs text-center" style={{ color: C.soft }}>Seul le magasinier ou l'administrateur peut enregistrer une révision.</p>
          )}

          {canEtat && !confirm && (
            confirmReforme ? (
              <div className="mt-3 rounded-lg px-3 py-3" style={{ border: `1px dashed ${C.red}` }}>
                <Field label="Motif de la réforme (obligatoire)">
                  <input style={inputStyle} value={motifReforme} onChange={(e2) => setMotifReforme(e2.target.value)} placeholder="Ex. cuve percée, moteur HS irréparable" />
                </Field>
                <p className="text-xs mb-3" style={{ color: C.soft }}>
                  Le matériel sort définitivement du parc actif. Il reste consultable dans l'onglet Réformé.
                </p>
                <div className="flex gap-2">
                  <button onClick={() => { setConfirmReforme(false); setMotifReforme(''); }}
                    className="flex-1 rounded-lg py-2 text-sm font-semibold" style={{ background: C.steelSoft, color: C.soft }}>
                    Annuler
                  </button>
                  <button disabled={!motifReforme.trim()} onClick={() => onReformer(u, motifReforme.trim())}
                    className="flex-1 rounded-lg py-2 text-sm font-semibold"
                    style={{ background: motifReforme.trim() ? C.red : C.border, color: motifReforme.trim() ? '#fff' : C.soft }}>
                    Réformer
                  </button>
                </div>
              </div>
            ) : (
              <button onClick={() => setConfirmReforme(true)} className="w-full mt-3 text-xs font-semibold flex items-center justify-center gap-1.5" style={{ color: C.red }}>
                <Archive size={13} /> Réformer ce matériel (non réparable)
              </button>
            )
          )}
        </>
      )}

      {modifierEtat && (
        <EtatSheet
          unit={u}
          onClose={() => setModifierEtat(false)}
          onSave={(etatChoisi, commentaire) => onChangerEtat(u, etatChoisi, commentaire)}
        />
      )}
    </Sheet>
  );
}

function Row({ k, v, tone }) {
  return (
    <div className="flex justify-between gap-3">
      <dt className="text-xs" style={{ color: C.soft }}>{k}</dt>
      <dd className="text-sm font-medium text-right" style={{ color: tone || C.ink }}>{v}</dd>
    </div>
  );
}

/* =================== FORMULAIRES =================== */

function UnitForm({ onClose, onSave }) {
  const [type, setType] = useState(TYPES_MATERIEL[0]);
  const [name, setName] = useState('');
  const [tag, setTag] = useState('');
  const [dateRevision, setDateRevision] = useState(todayISO());
  return (
    <Sheet title="Nouvelle unité de matériel" onClose={onClose}>
      <Field label="Famille de matériel">
        <select style={inputStyle} value={type} onChange={(e) => setType(e.target.value)}>
          {TYPES_MATERIEL.map((t) => <option key={t} value={t}>{t}</option>)}
          <option value="Autre">Autre</option>
        </select>
      </Field>
      <Field label="Désignation">
        <input style={inputStyle} value={name} onChange={(e) => setName(e.target.value)} placeholder="Ex. Aspirateur BEAR 200 H" />
      </Field>
      <Field label="Numéro de série (optionnel)">
        <input style={inputStyle} value={tag} onChange={(e) => setTag(e.target.value)} placeholder="Ex. ASP-04" />
      </Field>
      <Field label="Date de la dernière révision">
        <DatePicker value={dateRevision} onChange={setDateRevision} />
      </Field>
      <p className="text-xs mb-3" style={{ color: C.soft }}>
        Péremption au {frDate(addDays(dateRevision || todayISO(), REVISION_JOURS))}. Passée cette date, l'unité bascule automatiquement en quarantaine et ne peut plus être commandée.
      </p>
      <PrimaryButton disabled={!name.trim() || !dateRevision} onClick={() => onSave({ type, name: name.trim(), tag: tag.trim(), dateRevision })}>
        Enregistrer l'unité
      </PrimaryButton>
    </Sheet>
  );
}

function RefForm({ reference, onClose, onSave }) {
  const edit = !!reference;
  const [name, setName] = useState(edit ? reference.name : '');
  const [unit, setUnit] = useState(edit ? reference.unit : 'u');
  const [quantity, setQuantity] = useState(edit ? reference.quantity : 0);
  const [seuil, setSeuil] = useState(edit ? reference.seuil : 10);
  return (
    <Sheet title={edit ? reference.name : 'Nouvelle référence consommable'} onClose={onClose}>
      <Field label="Désignation">
        <input style={inputStyle} value={name} onChange={(e) => setName(e.target.value)} placeholder="Ex. Combinaison type 5/6" />
      </Field>
      <div className="grid grid-cols-2 gap-3">
        <Field label="Quantité en stock">
          <input type="number" min="0" style={inputStyle} value={quantity} onChange={(e) => setQuantity(Math.max(0, Number(e.target.value)))} />
        </Field>
        <Field label="Unité">
          <select style={inputStyle} value={unit} onChange={(e) => setUnit(e.target.value)}>
            {UNITES.map((u) => <option key={u} value={u}>{u}</option>)}
          </select>
        </Field>
      </div>
      <Field label="Seuil d'alerte">
        <input type="number" min="0" style={inputStyle} value={seuil} onChange={(e) => setSeuil(Math.max(0, Number(e.target.value)))} />
      </Field>
      <PrimaryButton disabled={!name.trim()} onClick={() => onSave({ name: name.trim(), unit, quantity, seuil })}>
        {edit ? 'Enregistrer les modifications' : 'Enregistrer la référence'}
      </PrimaryButton>
    </Sheet>
  );
}

function OutilForm({ onClose, onSave }) {
  const [name, setName] = useState('');
  return (
    <Sheet title="Nouvel outillage" onClose={onClose}>
      <Field label="Désignation">
        <input style={inputStyle} value={name} onChange={(e) => setName(e.target.value)} placeholder="Ex. Burineur t500" />
      </Field>
      <p className="text-xs mb-3" style={{ color: C.soft }}>
        Aucun stock ni révision ne sera suivi. L'article apparaîtra dans l'onglet Outillage des commandes.
      </p>
      <PrimaryButton disabled={!name.trim()} onClick={() => onSave({ name: name.trim() })}>
        Enregistrer l'outillage
      </PrimaryButton>
    </Sheet>
  );
}

function CommandePage({ type, affaires, units, refs, outils, onCancel, onSave }) {
  const ouvertes = affaires.filter((a) => a.ouverte);
  const isAppoint = type === 'appoint';
  const minLivraison = premiereLivraison();

  const [affaireId, setAffaireId] = useState(ouvertes.length ? ouvertes[0].id : '');
  const [dateLivraison, setDateLivraison] = useState(minLivraison);
  const [note, setNote] = useState('');
  const [unitIds, setUnitIds] = useState([]);
  const [consos, setConsos] = useState({});
  const [outilsQty, setOutilsQty] = useState({});
  const [vue, setVue] = useState('materiel');
  const [search, setSearch] = useState('');
  const [famille, setFamille] = useState('toutes');
  const [selOnly, setSelOnly] = useState(false);

  const dispo = units.filter(estCommandable);
  const bloques = units.filter((u) => ['hs', 'perime'].includes(etatUnite(u).key));

  const matches = (t) => t.toLowerCase().includes(search.toLowerCase());
  const familles = Array.from(new Set(dispo.map((u) => u.type || 'Autre'))).sort();
  const listeMat = dispo
    .filter((u) => famille === 'toutes' || (u.type || 'Autre') === famille)
    .filter((u) => matches(u.name + ' ' + (u.tag || '')))
    .filter((u) => !selOnly || unitIds.includes(u.id));
  const listeConso = refs
    .filter((r) => matches(r.name))
    .filter((r) => !selOnly || consos[r.id] > 0);
  const listeOutils = outils
    .filter((o) => matches(o.name))
    .filter((o) => !selOnly || outilsQty[o.id] > 0);

  const nbConso = Object.values(consos).filter((q) => q > 0).length;
  const nbOutils = Object.values(outilsQty).filter((q) => q > 0).length;
  const total = unitIds.length + nbConso + nbOutils;
  const dateOk = !!dateLivraison && dateLivraison >= minLivraison;
  const pret = total > 0 && dateOk && affaireId;

  const setQ = (id, q, max) => setConsos({ ...consos, [id]: Math.max(0, Math.min(max, q)) });

  return (
    <div className="min-h-screen pb-36" style={{ background: C.bg, color: C.ink }}>
      <header style={{ background: isAppoint ? C.green : C.steel }} className="px-5 pt-5 pb-4 sticky top-0 z-20">
        <button onClick={onCancel} className="flex items-center gap-1 text-sm mb-2" style={{ color: 'rgba(255,255,255,0.72)' }}>
          <ArrowLeft size={16} /> Annuler
        </button>
        <h1 className="font-bold text-base" style={{ color: '#fff' }}>{TYPES_CMD[type].label}</h1>
        <p className="text-xs mt-0.5" style={{ color: 'rgba(255,255,255,0.72)' }}>
          {total === 0
            ? 'Aucune ligne sélectionnée'
            : `${unitIds.length} matériel · ${nbConso} consommable${nbConso > 1 ? 's' : ''} · ${nbOutils} outillage`}
        </p>
      </header>

      {ouvertes.length === 0 ? (
        <p className="px-5 mt-6 text-sm" style={{ color: C.soft }}>
          Aucune affaire ouverte. Le chargé d'affaires doit en ouvrir une avant toute commande.
        </p>
      ) : (
        <>
          <div className="px-5 mt-4">
            <Field label="Affaire">
              <select style={inputStyle} value={affaireId} onChange={(e) => setAffaireId(e.target.value)}>
                {ouvertes.map((a) => <option key={a.id} value={a.id}>{a.numero} — {a.libelle}</option>)}
              </select>
            </Field>

            <Field label="Date de livraison souhaitée">
              <DatePicker value={dateLivraison} onChange={setDateLivraison} min={minLivraison} />
            </Field>
            <p className="text-xs -mt-1 mb-3" style={{ color: dateOk ? C.soft : C.red }}>
              {dateOk
                ? `Au plus tôt le ${frDate(minLivraison)} — ${DELAI_LIVRAISON_H} h de préparation, pas de livraison le jour même.`
                : `Impossible : pas de livraison avant le ${frDate(minLivraison)}.`}
            </p>

            <Field label={isAppoint ? 'Motif de la demande' : 'Consigne pour le magasinier (optionnel)'}>
              <input style={inputStyle} value={note} onChange={(e) => setNote(e.target.value)}
                placeholder={isAppoint ? 'Ex. rupture de combinaisons' : 'Ex. prévoir sas complet'} />
            </Field>
          </div>

          <div className="sticky top-[104px] z-10 px-5 pt-2 pb-3" style={{ background: C.bg, borderBottom: `1px solid ${C.border}` }}>
            <div className="flex gap-2 mb-2">
              {[
                { id: 'materiel', label: `Matériel (${unitIds.length})`, icon: Wrench },
                { id: 'conso', label: `Conso. (${nbConso})`, icon: Package },
                { id: 'outils', label: `Outillage (${nbOutils})`, icon: Hammer },
              ].map((t) => {
                const Icon = t.icon, on = vue === t.id;
                return (
                  <button key={t.id} onClick={() => setVue(t.id)}
                    className="flex-1 rounded-lg py-2 text-xs font-semibold flex items-center justify-center gap-1.5"
                    style={{ background: on ? C.steel : C.surface, color: on ? '#fff' : C.soft, border: `1px solid ${on ? C.steel : C.border}` }}>
                    <Icon size={14} />{t.label}
                  </button>
                );
              })}
            </div>
            <div className="flex items-center gap-2 rounded-lg px-3 py-2" style={{ background: C.surface, border: `1px solid ${C.border}` }}>
              <Search size={15} color={C.soft} />
              <input value={search} onChange={(e) => setSearch(e.target.value)}
                placeholder={vue === 'materiel' ? 'Rechercher un matériel…' : vue === 'conso' ? 'Rechercher une référence…' : 'Rechercher un outil…'}
                className="flex-1 outline-none text-sm bg-transparent" />
              {search && <button onClick={() => setSearch('')} aria-label="Effacer"><X size={15} color={C.soft} /></button>}
            </div>
            {vue === 'materiel' && familles.length > 1 && (
              <select value={famille} onChange={(e) => setFamille(e.target.value)}
                className="w-full mt-2 rounded-lg px-3 py-2 text-sm outline-none"
                style={{ background: C.surface, border: `1px solid ${famille === 'toutes' ? C.border : C.accent}`, color: C.ink }}>
                <option value="toutes">Toutes les familles ({dispo.length})</option>
                {familles.map((f) => (
                  <option key={f} value={f}>{f} ({dispo.filter((u) => (u.type || 'Autre') === f).length})</option>
                ))}
              </select>
            )}
            {total > 0 && (
              <button onClick={() => setSelOnly(!selOnly)} className="text-xs mt-2 font-semibold"
                style={{ color: selOnly ? C.accentInk : C.soft }}>
                {selOnly ? '← Revoir tout le catalogue' : `Voir uniquement ma sélection (${total})`}
              </button>
            )}
          </div>

          <div className="px-5 mt-3">
            {vue === 'outils' ? (
              <>
                {listeOutils.length === 0 && (
                  <p className="text-sm text-center py-8" style={{ color: C.soft }}>
                    {outils.length === 0 ? 'Aucun outillage enregistré.' : 'Aucun résultat.'}
                  </p>
                )}
                <p className="text-xs mb-2" style={{ color: C.soft }}>
                  Outillage de chantier : aucun stock n'est tenu, seule la quantité à charger est indiquée.
                </p>
                <div className="flex flex-col gap-2">
                  {listeOutils.map((o) => {
                    const q = outilsQty[o.id] || 0;
                    const on = q > 0;
                    return (
                      <div key={o.id} className="rounded-lg px-4 py-3 flex items-center justify-between gap-3"
                        style={{ background: on ? C.accentSoft : C.surface, border: `1px solid ${on ? C.accent : C.border}` }}>
                        <p className="text-sm font-medium truncate min-w-0">{o.name}</p>
                        <div className="flex items-center gap-2 flex-shrink-0">
                          <button onClick={() => setOutilsQty({ ...outilsQty, [o.id]: Math.max(0, q - 1) })} disabled={q === 0}
                            className="rounded-lg text-lg font-bold" style={{ width: 34, height: 34, background: C.steelSoft, color: q === 0 ? C.border : C.steel }}>−</button>
                          <input type="number" min="0" value={q || ''} onChange={(e) => setOutilsQty({ ...outilsQty, [o.id]: Math.max(0, Number(e.target.value)) })}
                            className="text-center text-sm font-bold outline-none rounded"
                            style={{ width: 52, border: `1px solid ${C.border}`, padding: '6px 2px', background: '#FCFBF9' }} placeholder="0" />
                          <button onClick={() => setOutilsQty({ ...outilsQty, [o.id]: q + 1 })}
                            className="rounded-lg text-lg font-bold" style={{ width: 34, height: 34, background: C.steelSoft, color: C.steel }}>+</button>
                        </div>
                      </div>
                    );
                  })}
                </div>
              </>
            ) : vue === 'materiel' ? (
              <>
                {listeMat.length === 0 && (
                  <p className="text-sm text-center py-8" style={{ color: C.soft }}>
                    {dispo.length === 0 ? 'Aucune unité disponible au dépôt.' : 'Aucun résultat.'}
                  </p>
                )}
                <div className="flex flex-col gap-2">
                  {listeMat.map((u) => {
                    const on = unitIds.includes(u.id);
                    const e = etatUnite(u);
                    return (
                      <button key={u.id} onClick={() => setUnitIds(on ? unitIds.filter((i) => i !== u.id) : [...unitIds, u.id])}
                        className="text-left rounded-lg px-4 py-3 flex items-center justify-between gap-3"
                        style={{ background: on ? C.accentSoft : C.surface, border: `1px solid ${on ? C.accent : C.border}` }}>
                        <div className="min-w-0">
                          <p className="text-sm font-medium truncate">{u.name}</p>
                          <p className="text-xs" style={{ color: C.soft }}>
                            {u.type ? `${u.type} · ` : ''}{u.tag ? `${u.tag} · ` : ''}
                            {u.etat === 'sale' && <span style={{ color: C.amber }}>sale · </span>}
                            {e.key === 'bientot' ? <span style={{ color: C.amber }}>révision J−{e.j}</span> : `révision ${frDate(e.next)}`}
                          </p>
                        </div>
                        <div className="rounded flex items-center justify-center flex-shrink-0"
                          style={{ width: 24, height: 24, border: `2px solid ${on ? C.accent : C.border}`, background: on ? C.accent : 'transparent' }}>
                          {on && <Check size={14} color={C.ink} />}
                        </div>
                      </button>
                    );
                  })}
                </div>
                {bloques.length > 0 && !selOnly && (
                  <p className="text-[11px] mt-3" style={{ color: C.red }}>
                    {bloques.length} unité{bloques.length > 1 ? 's' : ''} en quarantaine, non commandable{bloques.length > 1 ? 's' : ''}.
                  </p>
                )}
              </>
            ) : (
              <>
                {listeConso.length === 0 && (
                  <p className="text-sm text-center py-8" style={{ color: C.soft }}>
                    {refs.length === 0 ? 'Aucune référence enregistrée.' : 'Aucun résultat.'}
                  </p>
                )}
                <div className="flex flex-col gap-2">
                  {listeConso.map((r) => {
                    const q = consos[r.id] || 0;
                    const on = q > 0;
                    return (
                      <div key={r.id} className="rounded-lg px-4 py-3"
                        style={{ background: on ? C.accentSoft : C.surface, border: `1px solid ${on ? C.accent : C.border}` }}>
                        <div className="flex items-center justify-between gap-3">
                          <div className="min-w-0">
                            <p className="text-sm font-medium truncate">{r.name}</p>
                            <p className="text-xs" style={{ color: r.quantity <= r.seuil ? C.red : C.soft }}>
                              {r.quantity} {r.unit} en stock
                            </p>
                          </div>
                          <div className="flex items-center gap-2 flex-shrink-0">
                            <button onClick={() => setQ(r.id, q - 1, r.quantity)} disabled={q === 0}
                              className="rounded-lg text-lg font-bold" style={{ width: 34, height: 34, background: C.steelSoft, color: q === 0 ? C.border : C.steel }}>−</button>
                            <input type="number" min="0" max={r.quantity} value={q || ''}
                              onChange={(e) => setQ(r.id, Number(e.target.value), r.quantity)}
                              className="text-center text-sm font-bold outline-none rounded"
                              style={{ width: 52, border: `1px solid ${C.border}`, padding: '6px 2px', background: '#FCFBF9' }} placeholder="0" />
                            <button onClick={() => setQ(r.id, q + 1, r.quantity)} disabled={q >= r.quantity}
                              className="rounded-lg text-lg font-bold" style={{ width: 34, height: 34, background: C.steelSoft, color: q >= r.quantity ? C.border : C.steel }}>+</button>
                          </div>
                        </div>
                      </div>
                    );
                  })}
                </div>
              </>
            )}
          </div>
        </>
      )}

      {ouvertes.length > 0 && (
        <div className="fixed bottom-0 left-0 right-0 px-5 py-4" style={{ background: C.bg, borderTop: `1px solid ${C.border}` }}>
          <PrimaryButton disabled={!pret} color={isAppoint ? C.green : C.accent}
            onClick={() => onSave({
              type, affaireId, dateLivraison, note: note.trim(), unitIds,
              consos: Object.entries(consos).filter(([, q]) => q > 0).map(([refId, qty]) => ({ refId, qty })),
              outils: Object.entries(outilsQty).filter(([, q]) => q > 0).map(([outilId, qty]) => ({ outilId, qty })),
            })}>
            {isAppoint ? "Envoyer la demande d'appoint" : 'Créer la commande'}
            {total > 0 ? ` · ${total} ligne${total > 1 ? 's' : ''}` : ''}
          </PrimaryButton>
          {total === 0 && (
            <p className="text-[11px] text-center mt-2" style={{ color: C.soft }}>
              Sélectionnez au moins un matériel, un consommable ou un outil.
            </p>
          )}
        </div>
      )}
    </div>
  );
}

/* =================== AFFAIRES (affichées sur la page) =================== */

function AffairesInline({ affaires, commandes, canManage, selected, onSelect, onAdd, onToggle }) {
  const [form, setForm] = useState(false);
  const [voirCloturees, setVoirCloturees] = useState(false);
  const [numero, setNumero] = useState('');
  const [libelle, setLibelle] = useState('');
  const [adresse, setAdresse] = useState('');
  const ok = numero.trim() && libelle.trim();

  const ouvertes = affaires.filter((a) => a.ouverte);
  const cloturees = affaires.filter((a) => !a.ouverte);
  const enCours = (id) => commandes.filter((c) => c.affaireId === id && c.statut !== 'repliee').length;
  const [confirmerId, setConfirmerId] = useState(null);

  const Ligne = ({ a }) => {
    const on = selected === a.id;
    const n = enCours(a.id);
    const confirmation = confirmerId === a.id;
    return (
      <div className="rounded-lg overflow-hidden" style={{ border: `1px solid ${on ? C.accent : C.border}`, background: on ? C.accentSoft : C.surface }}>
        <div className="flex items-stretch">
          <button onClick={() => onSelect(on ? 'toutes' : a.id)} className="flex-1 text-left px-3 py-2.5 min-w-0">
            <div className="flex items-center gap-2">
              <span className="text-sm font-bold" style={{ color: on ? C.accentInk : C.ink }}>{a.numero}</span>
              {n > 0 && (
                <span className="text-[10px] font-semibold rounded-full px-1.5 py-0.5" style={{ background: C.steelSoft, color: C.steelMid }}>
                  {n} en cours
                </span>
              )}
            </div>
            <p className="text-xs truncate mt-0.5" style={{ color: C.soft }}>{a.libelle}</p>
            {a.adresse && <p className="text-[11px] truncate mt-0.5" style={{ color: C.soft }}>{a.adresse}</p>}
          </button>
          {canManage && (
            <button onClick={() => (a.ouverte ? setConfirmerId(confirmation ? null : a.id) : onToggle(a))}
              className="px-3 text-[10px] font-semibold flex-shrink-0"
              style={{ borderLeft: `1px solid ${C.border}`, color: a.ouverte ? C.soft : C.green }}>
              {a.ouverte ? (confirmation ? 'Annuler' : 'Clôturer') : 'Rouvrir'}
            </button>
          )}
        </div>
        {confirmation && (
          <div className="px-3 pb-3 pt-1" style={{ borderTop: `1px solid ${C.border}` }}>
            <p className="text-[11px] mt-2 mb-2" style={{ color: C.soft }}>
              Ses commandes seront déplacées vers l'onglet Archives et ne s'afficheront plus dans Commandes.
            </p>
            <button onClick={() => { onToggle(a); setConfirmerId(null); }}
              className="w-full rounded-lg py-2 text-xs font-semibold" style={{ background: C.steel, color: '#fff' }}>
              Confirmer la clôture de {a.numero}
            </button>
          </div>
        )}
      </div>
    );
  };

  return (
    <div className="mb-5">
      <div className="flex items-center justify-between mb-2">
        <div className="flex items-center gap-1.5">
          <Briefcase size={14} color={C.soft} />
          <h2 className="text-sm font-semibold" style={{ color: C.soft }}>
            Affaires ouvertes ({ouvertes.length})
          </h2>
        </div>
        {selected !== 'toutes' && (
          <button onClick={() => onSelect('toutes')} className="text-xs font-semibold" style={{ color: C.accentInk }}>
            Voir toutes
          </button>
        )}
      </div>

      <div className="flex flex-col gap-2">
        {ouvertes.length === 0 && (
          <p className="text-xs" style={{ color: C.soft }}>Aucune affaire ouverte. Ouvrez-en une pour pouvoir commander.</p>
        )}
        {ouvertes.map((a) => <Ligne key={a.id} a={a} />)}
      </div>

      {cloturees.length > 0 && (
        <>
          <button onClick={() => setVoirCloturees(!voirCloturees)} className="text-xs mt-2 flex items-center gap-1" style={{ color: C.soft }}>
            {voirCloturees ? <ChevronUp size={13} /> : <ChevronDown size={13} />}
            {cloturees.length} affaire{cloturees.length > 1 ? 's' : ''} clôturée{cloturees.length > 1 ? 's' : ''}
          </button>
          {voirCloturees && (
            <div className="flex flex-col gap-2 mt-2" style={{ opacity: 0.6 }}>
              {cloturees.map((a) => <Ligne key={a.id} a={a} />)}
            </div>
          )}
        </>
      )}

      {canManage && (
        form ? (
          <div className="rounded-lg px-3 py-3 mt-2" style={{ background: C.surface, border: `1px dashed ${C.border}` }}>
            <div className="grid grid-cols-3 gap-2 mb-2">
              <input style={{ ...inputStyle, gridColumn: 'span 1' }} value={numero} onChange={(e) => setNumero(e.target.value)} placeholder="A-2607" />
              <input style={{ ...inputStyle, gridColumn: 'span 2' }} value={libelle} onChange={(e) => setLibelle(e.target.value)} placeholder="Libellé du chantier" />
            </div>
            <input style={inputStyle} className="mb-2" value={adresse} onChange={(e) => setAdresse(e.target.value)}
              placeholder="Adresse de livraison (optionnel)" />
            <div className="flex gap-2">
              <button onClick={() => { setForm(false); setNumero(''); setLibelle(''); setAdresse(''); }}
                className="flex-1 rounded-lg py-2 text-sm font-semibold" style={{ background: C.steelSoft, color: C.soft }}>
                Annuler
              </button>
              <button disabled={!ok}
                onClick={() => { onAdd({ numero: numero.trim(), libelle: libelle.trim(), adresse: adresse.trim() }); setNumero(''); setLibelle(''); setAdresse(''); setForm(false); }}
                className="flex-1 rounded-lg py-2 text-sm font-semibold"
                style={{ background: ok ? C.accent : C.border, color: ok ? C.ink : C.soft }}>
                Ouvrir
              </button>
            </div>
          </div>
        ) : (
          <button onClick={() => setForm(true)} className="text-xs mt-2 flex items-center gap-1.5 font-semibold" style={{ color: C.accentInk }}>
            <Plus size={14} /> Ouvrir une affaire
          </button>
        )
      )}
    </div>
  );
}

/* =================== NOTIFICATION COMMANDE (initiale ou appoint) =================== */

function NotifierSheet({ commande: c, users, units, refs, onClose, onSent }) {
  const dest = users.filter((u) => ['magasinier', 'conducteur', 'admin'].includes(u.role) && u.email);
  const sansMail = users.filter((u) => ['magasinier', 'conducteur', 'admin'].includes(u.role) && !u.email);
  const unitById = Object.fromEntries(units.map((u) => [u.id, u]));
  const refById = Object.fromEntries(refs.map((r) => [r.id, r]));
  const libelleType = TYPES_CMD[c.type].label;

  const [statut, setStatut] = useState('sending'); // 'sending' | 'envoye' | 'erreur'
  const envoyeRef = useRef(null);

  const corps = [
    `${libelleType} ${c.num}`,
    `Affaire : ${c.chantier}`,
    c.adresse ? `Adresse de livraison : ${c.adresse}` : '',
    `Demandeur : ${c.demandeur}`,
    `Livraison souhaitee : ${frDate(c.dateLivraison)}`,
    c.note ? `Motif : ${c.note}` : '',
    '',
    'Materiel :',
    ...(c.unitIds.length ? c.unitIds.map((id) => `- ${unitById[id] ? unitById[id].name : id}`) : ['- neant']),
    '',
    'Consommables :',
    ...(c.consos.length ? c.consos.map((l) => `- ${refById[l.refId] ? refById[l.refId].name : l.refId} : ${l.qty}`) : ['- neant']),
    '',
    `Rappel : pas de livraison le jour meme, ${DELAI_LIVRAISON_H} h de preparation minimum.`,
  ].join('\n');

  const subject = `[APII] ${libelleType} ${c.num} — ${c.chantier}`;
  const mailto = `mailto:${dest.map((u) => u.email).join(',')}?subject=${encodeURIComponent(subject)}&body=${encodeURIComponent(corps)}`;

  useEffect(() => {
    if (envoyeRef.current === c.id) return; // évite un double envoi (ex. StrictMode)
    envoyeRef.current = c.id;
    if (!dest.length || !supabase) { setStatut('erreur'); return; }
    (async () => {
      try {
        const { data, error } = await supabase.functions.invoke('send-commande-email', {
          body: { to: dest.map((u) => u.email), subject, text: corps },
        });
        if (error || !data || data.ok !== true) throw error || new Error('echec envoi');
        setStatut('envoye');
        onSent(c, dest.length);
      } catch (e) {
        setStatut('erreur');
      }
    })();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [c.id]);

  return (
    <Sheet title={`${c.num} enregistrée`} onClose={onClose}>
      <div className="rounded-lg px-4 py-3 mb-4 text-sm" style={{ background: C.greenSoft, color: C.green }}>
        La demande est visible immédiatement dans l'application pour le magasinier et le chargé d'affaires.
      </div>
      <SectionTitle icon={Mail} label={`Destinataires (${dest.length})`} />
      <div className="flex flex-col gap-1.5 mb-3">
        {dest.map((u) => (
          <div key={u.id} className="text-xs rounded-md px-3 py-2" style={{ background: '#FCFBF9', border: `1px solid ${C.border}` }}>
            {u.name} · <span style={{ color: C.soft }}>{u.email}</span>
          </div>
        ))}
        {dest.length === 0 && <p className="text-xs" style={{ color: C.soft }}>Aucun destinataire : les profils concernés n'ont pas d'adresse e-mail renseignée.</p>}
      </div>
      {sansMail.length > 0 && (
        <p className="text-[11px] mb-3" style={{ color: C.amber }}>
          {sansMail.length} profil{sansMail.length > 1 ? 's' : ''} sans adresse e-mail ne sera{sansMail.length > 1 ? 'ont' : ''} pas prévenu{sansMail.length > 1 ? 's' : ''} par mail.
        </p>
      )}

      {statut === 'sending' && (
        <div className="rounded-lg py-2.5 text-sm font-semibold text-center flex items-center justify-center gap-2"
          style={{ background: C.steelSoft, color: C.soft }}>
          <Loader2 size={16} className="animate-spin" /> Envoi de la notification…
        </div>
      )}
      {statut === 'envoye' && (
        <div className="rounded-lg py-2.5 text-sm font-semibold text-center flex items-center justify-center gap-2"
          style={{ background: C.greenSoft, color: C.green }}>
          <CircleCheck size={16} /> Notification envoyée à {dest.length} destinataire{dest.length > 1 ? 's' : ''}
        </div>
      )}
      {statut === 'erreur' && (
        <>
          <div className="rounded-lg px-4 py-3 mb-2 text-xs" style={{ background: C.amberSoft, color: C.amber }}>
            L'envoi automatique n'a pas fonctionné (service de messagerie non configuré ou indisponible). Utilisez le lien ci-dessous en secours.
          </div>
          <a href={dest.length ? mailto : undefined} onClick={() => dest.length && onSent(c, dest.length)}
            className="block w-full rounded-lg py-2.5 text-sm font-semibold text-center"
            style={{ background: dest.length ? C.accent : C.border, color: dest.length ? C.ink : C.soft, pointerEvents: dest.length ? 'auto' : 'none' }}>
            <span className="flex items-center justify-center gap-2"><Send size={16} /> Préparer l'e-mail manuellement</span>
          </a>
        </>
      )}
    </Sheet>
  );
}

/* =================== EXPORT PDF (bon de livraison / repli) =================== */

function telechargerPdf(contenu, nomFichier) {
  const buf = new Uint8Array(contenu.length);
  for (let i = 0; i < contenu.length; i++) buf[i] = contenu.charCodeAt(i) & 0xff;
  const blob = new Blob([buf], { type: 'application/pdf' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url; a.download = nomFichier;
  document.body.appendChild(a); a.click(); document.body.removeChild(a);
  setTimeout(() => URL.revokeObjectURL(url), 4000);
}

/* Fiche matériel — indépendante du bon de commande. QR, état, révisions,
   historique d'utilisation et de réparations pour une seule unité. */
function genererPdfMateriel(u, journal, commandes, urlPublique) {
  const marginX = 42, rightX = 553;
  const doc = new PdfDoc();
  let y = 46;
  doc.addPage();
  doc.texte(marginX, y, 'STOCK APII', { size: 16, gras: true });
  doc.texte(rightX - 100, y, 'Fiche matériel', { size: 9, couleur: [0.43, 0.41, 0.37] });
  y += 10;
  doc.ligneH(marginX, y, rightX, 0.6);
  y += 26;

  const qrSize = 70;
  doc.qr(matriceQR(codeQR('M', u.id, urlPublique)), rightX - qrSize, y - 8, qrSize);

  doc.texte(marginX, y, u.name, { size: 15, gras: true });
  y += 17;
  const e = etatUnite(u);
  const lignesIdentite = [
    u.type ? `Famille : ${u.type}` : null,
    `N° de série : ${u.tag || '—'}`,
    `État : ${e.label}`,
    `Dernière révision : ${frDate(u.dateRevision)}  ·  Prochaine échéance : ${frDate(e.next)}`,
    u.derniereFacture ? `N° de facture (dernière révision) : ${u.derniereFacture}` : null,
  ].filter(Boolean);
  for (const l of lignesIdentite) { doc.texte(marginX, y, l, { size: 10, couleur: [0.43, 0.41, 0.37] }); y += 13; }
  y += 6;

  if (u.lienNotice) { doc.texte(marginX, y, `Notice d'utilisation : ${u.lienNotice}`, { size: 9, couleur: [0.24, 0.40, 0.58] }); y += 13; }
  if (u.lienFicheRevision) { doc.texte(marginX, y, `Fiche de révision : ${u.lienFicheRevision}`, { size: 9, couleur: [0.24, 0.40, 0.58] }); y += 13; }
  y += 10;

  const sautDePage = (needed) => {
    if (y + needed > 800) {
      doc.addPage(); y = 46;
      doc.texte(marginX, y, 'STOCK APII', { size: 13, gras: true });
      doc.texte(rightX - 130, y, `Fiche matériel (suite) — ${u.name}`, { size: 9, couleur: [0.43, 0.41, 0.37] });
      y += 22;
    }
  };
  const titre = (t) => {
    sautDePage(30);
    doc.rectPlein(marginX, y - 10, rightX - marginX, 16, [0.91, 0.91, 0.89]);
    doc.texte(marginX + 4, y, t, { size: 11, gras: true });
    y += 20;
  };

  /* Comparaison au libellé exact (nom + n° de série) : plusieurs unités importées
     partagent la même désignation — un simple "includes" mélangerait leurs historiques. */
  const libelleUnite = u.name + (u.tag ? ` · ${u.tag}` : '');
  const revisions = journal.filter((j) => j.type === 'revision' && j.label === libelleUnite);
  titre(`Révisions enregistrées (${revisions.length})`);
  if (!revisions.length) {
    doc.texte(marginX, y, 'Aucune révision enregistrée.', { size: 9.5, couleur: [0.43, 0.41, 0.37] }); y += 16;
  }
  for (const r of revisions) {
    const lignesDetail = retourALaLigne(r.detail || '', 9, false, rightX - marginX);
    sautDePage(14 + lignesDetail.length * 11 + 4);
    doc.texte(marginX, y, `${frDateHeure(r.date)}${r.par ? ' — ' + r.par : ''}`, { size: 9, gras: true }); y += 12;
    lignesDetail.forEach((l) => { doc.texte(marginX, y, l, { size: 9, couleur: [0.43, 0.41, 0.37] }); y += 11; });
    y += 3;
  }
  y += 6;

  const passages = (commandes || [])
    .filter((c) => c.charge && c.charge.unitIds.includes(u.id))
    .map((c) => ({
      num: c.num, chantier: c.chantier, depart: c.chargeAt, retour: c.repliAt,
      etat: c.repli && c.repli.units[u.id] ? c.repli.units[u.id].etat : null,
      commentaire: c.repli && c.repli.units[u.id] ? c.repli.units[u.id].comment : '',
    }))
    .sort((a, b) => (b.depart || '').localeCompare(a.depart || ''));

  titre(`Historique d'utilisation et de réparations (${passages.length})`);
  if (!passages.length) {
    doc.texte(marginX, y, "Cette unité n'est encore jamais partie en chantier.", { size: 9.5, couleur: [0.43, 0.41, 0.37] }); y += 16;
  }
  for (const p of passages) {
    const ligneRetour = p.etat ? `Retour ${ETATS[p.etat].label.toLowerCase()}${p.commentaire ? ' — ' + p.commentaire : ''}` : '';
    const lignesRetour = ligneRetour ? retourALaLigne(ligneRetour, 9, false, rightX - marginX) : [];
    sautDePage(24 + lignesRetour.length * 12 + 6);
    doc.texte(marginX, y, `${p.chantier} — ${p.num}`, { size: 9.5, gras: true }); y += 12;
    const ligne = `Parti le ${frDateHeure(p.depart)}` + (p.retour ? ` · rentré le ${frDateHeure(p.retour)}` : ' · toujours sur chantier');
    doc.texte(marginX, y, ligne, { size: 9, couleur: [0.43, 0.41, 0.37] }); y += 12;
    if (lignesRetour.length) {
      const cc = p.etat === 'hs' ? [0.70, 0.23, 0.05] : p.etat === 'sale' ? [0.60, 0.42, 0.06] : [0.21, 0.45, 0.25];
      lignesRetour.forEach((l) => { doc.texte(marginX, y, l, { size: 9, couleur: cc }); y += 12; });
    } else { y += 3; }
    doc.ligneH(marginX, y - 4, rightX, 0.4);
  }

  const nomPropre = `Fiche de vie - ${u.name}${u.tag ? ' - ' + u.tag : ''}`.replace(/[\\/:*?"<>|]+/g, '-');
  telechargerPdf(doc.bytes(), `${nomPropre}.pdf`);
}

function genererPdfCommande(c, unitById, refById, outilById, urlPublique) {
  const marginX = 42, rightX = 553, qrSize = 40;
  const doc = new PdfDoc();
  let y = 0;

  const enTete = (suite) => {
    doc.addPage();
    y = 46;
    doc.texte(marginX, y, 'STOCK APII', { size: 16, gras: true });
    doc.texte(rightX - 90, y, (c.type === 'appoint' ? "Bon d'appoint" : 'Bon de commande') + (suite ? ' (suite)' : ''), { size: 9, couleur: [0.43, 0.41, 0.37] });
    y += 10;
    doc.ligneH(marginX, y, rightX, 0.6);
    y += 18;
    doc.texte(marginX, y, c.num, { size: 13, gras: true });
    y += 14;
    doc.texte(marginX, y, `Affaire : ${c.chantier}`, { size: 9.5 }); y += 12;
    doc.texte(marginX, y, `Demandeur : ${c.demandeur}`, { size: 9.5 }); y += 12;
    if (c.chargeAt) { doc.texte(marginX, y, `Livré le : ${frDateHeure(c.chargeAt)}${c.chargePar ? ' par ' + c.chargePar : ''}`, { size: 9.5 }); y += 12; }
    if (c.repliAt) { doc.texte(marginX, y, `Replié le : ${frDateHeure(c.repliAt)}${c.repliPar ? ' par ' + c.repliPar : ''}`, { size: 9.5 }); y += 12; }
    y += 8;
  };
  enTete(false);

  const sautDePage = (needed) => { if (y + needed > 800) enTete(true); };
  const titreSection = (t) => {
    sautDePage(30);
    doc.rectPlein(marginX, y - 10, rightX - marginX, 16, [0.91, 0.91, 0.89]);
    doc.texte(marginX + 4, y, t, { size: 11, gras: true });
    y += 20;
  };

  // Matériel — QR à droite de chaque ligne
  const materiel = (c.unitIds || []).map((id) => unitById[id]).filter(Boolean);
  if (materiel.length) {
    titreSection('Matériel');
    const rowH = 48;
    for (const u of materiel) {
      sautDePage(rowH + 6);
      const debut = y;
      doc.texte(marginX, y, u.name, { size: 10, gras: true });
      doc.texte(marginX, y + 12, u.tag ? `N° de série : ${u.tag}` : 'Sans numéro de série', { size: 9, couleur: [0.43, 0.41, 0.37] });
      const back = c.repli.units[u.id];
      if (back) {
        const cc = back.etat === 'hs' ? [0.70, 0.23, 0.05] : back.etat === 'sale' ? [0.60, 0.42, 0.06] : [0.21, 0.45, 0.25];
        doc.texte(marginX, y + 24, `Retour : ${ETATS[back.etat].label}${back.comment ? ' — ' + back.comment : ''}`, { size: 9, couleur: cc });
      }
      doc.qr(matriceQR(codeQR('M', u.id, urlPublique)), rightX - qrSize, debut - 20, qrSize);
      y += rowH;
      doc.ligneH(marginX, y - 6, rightX, 0.4);
    }
    y += 6;
  }

  // Consommables — QR à droite également
  const consos = (c.consos || []).map((l) => ({ ...l, ref: refById[l.refId] })).filter((l) => l.ref);
  if (consos.length) {
    titreSection('Consommables');
    const rowH = 40;
    for (const l of consos) {
      sautDePage(rowH + 6);
      const debut = y;
      const outQ = c.charge.consos[l.refId] || 0;
      const backQ = c.repli.consos[l.refId];
      doc.texte(marginX, y, l.ref.name, { size: 10, gras: true });
      let detail = `Demandé : ${l.qty} ${l.ref.unit}`;
      if (c.statut !== 'a_preparer') detail += ` · Chargé : ${outQ}`;
      if (backQ !== undefined) detail += ` · Rentré : ${backQ} · Consommé : ${outQ - backQ}`;
      doc.texte(marginX, y + 12, detail, { size: 9, couleur: [0.43, 0.41, 0.37] });
      doc.qr(matriceQR(codeQR('C', l.refId, urlPublique)), rightX - qrSize, debut - 14, qrSize);
      y += rowH;
      doc.ligneH(marginX, y - 6, rightX, 0.4);
    }
    y += 6;
  }

  // Outillage — sans QR, ni stock ni suivi
  const outilsLignes = (c.outils || []).map((l) => ({ ...l, outil: outilById[l.outilId] })).filter((l) => l.outil);
  if (outilsLignes.length) {
    titreSection('Outillage (sans QR)');
    for (const l of outilsLignes) {
      sautDePage(18);
      const outQ = (c.charge.outils || {})[l.outilId];
      const backQ = (c.repli.outils || {})[l.outilId];
      let detail = `${l.outil.name} — demandé ${l.qty}`;
      if (outQ !== undefined) detail += ` · chargé ${outQ}`;
      if (backQ !== undefined) detail += ` · rentré ${backQ}`;
      doc.texte(marginX, y, detail, { size: 9.5 });
      y += 14;
    }
  }

  const slug = (c.chantier || '').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/(^-|-$)/g, '');
  telechargerPdf(doc.bytes(), `${c.num}${slug ? '-' + slug : ''}.pdf`);
}

/* =================== DÉTAIL COMMANDE =================== */

function CommandeDetail({ commande: c, units, refs, outils, canScan, urlPublique, onBack, onScan }) {
  const st = STATUTS[c.statut];
  const [exportEnCours, setExportEnCours] = useState(false);
  const unitById = Object.fromEntries(units.map((u) => [u.id, u]));
  const refById = Object.fromEntries(refs.map((r) => [r.id, r]));
  const outilById = Object.fromEntries((outils || []).map((o) => [o.id, o]));

  function exporterPdf() {
    setExportEnCours(true);
    // Laisse le bouton se redessiner avant un calcul qui peut prendre un instant
    // sur une longue commande (plusieurs QR à recalculer).
    setTimeout(() => {
      try { genererPdfCommande(c, unitById, refById, outilById, urlPublique); }
      finally { setExportEnCours(false); }
    }, 30);
  }

  return (
    <div className="min-h-screen pb-28" style={{ background: C.bg, color: C.ink }}>
      <header style={{ background: C.steel }} className="px-5 pt-5 pb-4 sticky top-0 z-20">
        <button onClick={onBack} className="flex items-center gap-1 text-sm mb-3" style={{ color: '#B3B3B1' }}>
          <ArrowLeft size={16} /> Commandes
        </button>
        <div className="flex items-center justify-between gap-2">
          <div className="flex items-center gap-2 min-w-0">
            <h1 className="font-bold text-lg" style={{ color: '#fff' }}>{c.num}</h1>
            {c.type === 'appoint' && (
              <span className="text-[10px] font-semibold rounded px-1.5 py-0.5" style={{ background: C.greenSoft, color: C.green }}>APPOINT</span>
            )}
          </div>
          <span className="text-[11px] font-semibold rounded px-2 py-0.5" style={{ background: st.soft, color: st.color }}>{st.label}</span>
        </div>
        <p className="text-sm mt-0.5" style={{ color: '#E4E4E2' }}>{c.chantier}</p>
        <p className="text-xs mt-0.5" style={{ color: '#A3A3A1' }}>
          Demandée par {c.demandeur}{c.dateLivraison ? ` · livraison ${frDate(c.dateLivraison)}` : ''}
          {c.chargePar ? ` · chargée par ${c.chargePar}` : ''}
          {c.repliPar ? ` · repliée par ${c.repliPar}` : ''}
        </p>
      </header>

      <div className="px-5 mt-4">
        {c.note && <div className="rounded-lg px-4 py-3 mb-4 text-sm" style={{ background: C.amberSoft, color: C.amber }}>{c.note}</div>}

        <SectionTitle icon={Wrench} label="Matériel" />
        <div className="flex flex-col gap-2 mb-5">
          {c.unitIds.length === 0 && <p className="text-xs" style={{ color: C.soft }}>Aucun matériel sur cette commande.</p>}
          {c.unitIds.map((id) => {
            const u = unitById[id];
            if (!u) return null;
            const loaded = c.charge.unitIds.includes(id);
            const back = c.repli.units[id];
            return (
              <div key={id} className="rounded-lg px-4 py-3 flex items-center justify-between gap-3" style={{ background: C.surface, border: `1px solid ${C.border}` }}>
                <div className="min-w-0">
                  <p className="text-sm font-medium truncate">{u.name}{u.tag ? ` · ${u.tag}` : ''}</p>
                  {back && (
                    <p className="text-xs" style={{ color: ETATS[back.etat].color }}>
                      Rentré {ETATS[back.etat].label.toLowerCase()}{back.comment ? ` — ${back.comment}` : ''}
                    </p>
                  )}
                </div>
                {loaded && !back && <Check size={16} color={C.green} />}
              </div>
            );
          })}
        </div>

        <SectionTitle icon={Package} label="Consommables" />
        <div className="flex flex-col gap-2">
          {c.consos.length === 0 && <p className="text-xs" style={{ color: C.soft }}>Aucun consommable sur cette commande.</p>}
          {c.consos.map((l) => {
            const r = refById[l.refId];
            if (!r) return null;
            const out = c.charge.consos[l.refId] || 0;
            const back = c.repli.consos[l.refId];
            return (
              <div key={l.refId} className="rounded-lg px-4 py-3" style={{ background: C.surface, border: `1px solid ${C.border}` }}>
                <div className="flex items-center justify-between gap-3">
                  <p className="text-sm font-medium truncate">{r.name}</p>
                  <p className="text-sm font-semibold">{l.qty} {r.unit}</p>
                </div>
                {c.statut !== 'a_preparer' && (
                  <p className="text-xs mt-0.5" style={{ color: C.soft }}>
                    {out} chargé{back !== undefined ? ` · ${back} rentré · ${out - back} consommé` : ''}
                  </p>
                )}
              </div>
            );
          })}
        </div>

        {(c.outils || []).length > 0 && (
          <>
            <div className="mt-5" />
            <SectionTitle icon={Hammer} label="Outillage" />
            <div className="flex flex-col gap-2">
              {(c.outils || []).map((l) => {
                const o = outilById[l.outilId];
                const out = (c.charge.outils || {})[l.outilId];
                const back = (c.repli.outils || {})[l.outilId];
                return (
                  <div key={l.outilId} className="rounded-lg px-4 py-3" style={{ background: C.surface, border: `1px solid ${C.border}` }}>
                    <div className="flex items-center justify-between gap-3">
                      <p className="text-sm font-medium truncate">{o ? o.name : 'Outil supprimé'}</p>
                      <p className="text-sm font-semibold">{l.qty}</p>
                    </div>
                    {c.statut !== 'a_preparer' && (
                      <p className="text-xs mt-0.5" style={{ color: back !== undefined && out !== undefined && back < out ? C.red : C.soft }}>
                        {out || 0} chargé{back !== undefined ? ` · ${back} rentré${back < (out || 0) ? ` · ${(out || 0) - back} manquant` : ''}` : ''}
                      </p>
                    )}
                  </div>
                );
              })}
            </div>
          </>
        )}
      </div>

      {(c.statut !== 'repliee' || c.statut === 'chargee' || c.statut === 'repliee') && (
        <div className="fixed bottom-0 left-0 right-0 px-5 py-4 flex flex-col gap-2" style={{ background: C.bg, borderTop: `1px solid ${C.border}` }}>
          {c.statut !== 'repliee' && (
            canScan ? (
              <PrimaryButton color={c.statut === 'a_preparer' ? C.accent : C.steel} onClick={() => onScan(c.statut === 'a_preparer' ? 'chargement' : 'repli')}>
                <span className="flex items-center justify-center gap-2">
                  <Camera size={16} />{c.statut === 'a_preparer' ? 'Scanner le chargement' : 'Scanner le repli'}
                </span>
              </PrimaryButton>
            ) : (
              <p className="text-xs text-center" style={{ color: C.soft }}>
                Le scan est réservé au magasinier.
              </p>
            )
          )}
          {(c.statut === 'chargee' || c.statut === 'repliee') && (
            <button onClick={exporterPdf} disabled={exportEnCours}
              className="w-full rounded-lg py-2.5 text-sm font-semibold flex items-center justify-center gap-2"
              style={{ border: `1px solid ${C.border}`, background: C.surface, color: C.ink }}>
              {exportEnCours ? <Loader2 className="animate-spin" size={15} /> : <FileDown size={16} />}
              {exportEnCours ? 'Génération du PDF…' : 'Extraire un PDF'}
            </button>
          )}
        </div>
      )}
    </div>
  );
}

/* =================== SESSION DE SCAN =================== */

function ScanSession({ mode, commande: c, units, refs, outils, onCancel, onValidate }) {
  const isCharge = mode === 'chargement';
  const unitById = Object.fromEntries(units.map((u) => [u.id, u]));
  const refById = Object.fromEntries(refs.map((r) => [r.id, r]));
  const outilById = Object.fromEntries((outils || []).map((o) => [o.id, o]));
  const chargeOutils = c.charge.outils || {};
  const expectedOutils = isCharge
    ? (c.outils || [])
    : Object.entries(chargeOutils).filter(([, q]) => q > 0).map(([outilId, qty]) => ({ outilId, qty }));

  const expectedUnits = isCharge ? c.unitIds : c.charge.unitIds;
  const expectedConsos = isCharge
    ? c.consos.map((l) => ({ refId: l.refId, qty: l.qty }))
    : Object.entries(c.charge.consos).map(([refId, qty]) => ({ refId, qty }));

  const [scannedUnits, setScannedUnits] = useState({});
  const [consoQty, setConsoQty] = useState({});
  const [outilsQty, setOutilsQty] = useState({});
  const [manual, setManual] = useState('');
  const [showManual, setShowManual] = useState(false);
  const [pendingEtat, setPendingEtat] = useState(null);
  const [pendingConso, setPendingConso] = useState(null);
  const [flash, setFlash] = useState(null);

  function notify(msg, tone = 'ok') {
    setFlash({ msg, tone });
    setTimeout(() => setFlash(null), 2200);
  }

  function handleCode(raw) {
    const code = (raw || '').trim();
    /* Le QR peut désormais être une simple étiquette interne (APII:M:id) ou
       une URL complète se terminant par #APII:M:id (pour l'ouverture directe
       sur smartphone) : on retrouve l'identifiant dans les deux cas. */
    const m = code.match(/APII:(M|C):([^#\s]+)$/);
    if (!m) { notify('QR non reconnu', 'err'); return; }
    const [, kind, id] = m;
    if (kind === 'M') {
      if (!expectedUnits.includes(id)) {
        notify(unitById[id] ? `${unitById[id].name} n'est pas sur cette commande` : 'Matériel inconnu', 'err');
        return;
      }
      if (scannedUnits[id]) { notify('Déjà scanné'); return; }
      if (isCharge) {
        const u = unitById[id];
        if (!estCommandable(u)) { notify(`${u.name} est en quarantaine — ne pas charger`, 'err'); return; }
        setScannedUnits((s) => ({ ...s, [id]: true }));
        notify(`${u.name} chargé`);
      } else {
        const u = unitById[id];
        /* Un masque n'a pas d'état propre/sale/HS à déclarer : il est repris
           tel quel, sans ouvrir le sélecteur d'état. */
        if (u && FAMILLES_MASQUE.has(u.type)) {
          setScannedUnits((s) => ({ ...s, [id]: { etat: 'propre', comment: '' } }));
          notify(`${u.name} rentré`);
        } else {
          setPendingEtat(id);
        }
      }
    } else {
      if (!expectedConsos.find((e) => e.refId === id)) { notify('Référence absente de la commande', 'err'); return; }
      setPendingConso(id);
    }
  }

  const done = expectedUnits.filter((id) => scannedUnits[id]).length
    + expectedConsos.filter((e) => consoQty[e.refId] !== undefined).length
    + expectedOutils.filter((l) => outilsQty[l.outilId] !== undefined).length;
  const total = expectedUnits.length + expectedConsos.length + expectedOutils.length;

  function validate() {
    if (isCharge) {
      onValidate({
        unitIds: Object.keys(scannedUnits),
        consos: Object.fromEntries(Object.entries(consoQty).filter(([, q]) => q > 0)),
        outils: outilsQty,
      });
    } else {
      onValidate({ units: scannedUnits, consos: consoQty, outils: outilsQty });
    }
  }

  return (
    <div className="min-h-screen pb-32" style={{ background: C.bg, color: C.ink }}>
      <header style={{ background: C.steel }} className="px-5 pt-5 pb-4 sticky top-0 z-20">
        <button onClick={onCancel} className="flex items-center gap-1 text-sm mb-2" style={{ color: '#B3B3B1' }}>
          <ArrowLeft size={16} /> Annuler
        </button>
        <h1 className="font-bold text-base" style={{ color: '#fff' }}>
          {isCharge ? 'Chargement camion' : 'Repli de chantier'} · {c.num}
        </h1>
        <p className="text-xs" style={{ color: '#B3B3B1' }}>{c.chantier} — {done}/{total} validé{done > 1 ? 's' : ''}</p>
        <div className="mt-2 h-1 rounded-full overflow-hidden" style={{ background: '#6B6B6B' }}>
          <div style={{ width: `${total ? (done / total) * 100 : 0}%`, height: '100%', background: C.accent }} />
        </div>
      </header>

      <div className="px-5 mt-4">
        <CameraScanner onCode={handleCode} />

        {flash && (
          <div className="rounded-lg px-4 py-2 mt-3 text-sm"
            style={{ background: flash.tone === 'err' ? C.redSoft : C.greenSoft, color: flash.tone === 'err' ? C.red : C.green }}>
            {flash.msg}
          </div>
        )}

        <button onClick={() => setShowManual(!showManual)} className="mt-3 text-xs flex items-center gap-1.5" style={{ color: C.steelMid }}>
          <Keyboard size={14} /> Saisir un code à la main
        </button>
        {showManual && (
          <div className="flex gap-2 mt-2">
            <input style={inputStyle} value={manual} onChange={(e) => setManual(e.target.value)} placeholder="APII:M:…" />
            <button onClick={() => { handleCode(manual); setManual(''); }} className="rounded-lg px-4 text-sm font-semibold flex-shrink-0" style={{ background: C.steel, color: '#fff' }}>
              OK
            </button>
          </div>
        )}

        <p className="text-xs mt-5 mb-2" style={{ color: C.soft }}>Touchez une ligne pour la valider sans scanner.</p>

        {expectedUnits.length > 0 && <SectionTitle icon={Wrench} label="Matériel" />}
        <div className="flex flex-col gap-2 mb-5">
          {expectedUnits.map((id) => {
            const u = unitById[id];
            if (!u) return null;
            const s = scannedUnits[id];
            const etat = !isCharge && s ? ETATS[s.etat] : null;
            return (
              <button key={id} onClick={() => !s && handleCode(codeFor('M', id))}
                className="text-left rounded-lg px-4 py-3 flex items-center justify-between gap-3"
                style={{ background: s ? (etat ? etat.soft : C.greenSoft) : C.surface, border: `1px solid ${s ? (etat ? etat.color : C.green) : C.border}` }}>
                <div className="min-w-0">
                  <p className="text-sm font-medium truncate">{u.name}{u.tag ? ` · ${u.tag}` : ''}</p>
                  {s && !isCharge && (
                    <p className="text-xs" style={{ color: etat.color }}>{etat.label}{s.comment ? ` — ${s.comment}` : ''}</p>
                  )}
                </div>
                {s ? <Check size={16} color={etat ? etat.color : C.green} /> : <QrCode size={16} color={C.soft} />}
              </button>
            );
          })}
        </div>

        {expectedConsos.length > 0 && <SectionTitle icon={Package} label="Consommables" />}
        <div className="flex flex-col gap-2">
          {expectedConsos.map((e) => {
            const r = refById[e.refId];
            if (!r) return null;
            const q = consoQty[e.refId];
            const set = q !== undefined;
            return (
              <button key={e.refId} onClick={() => setPendingConso(e.refId)}
                className="text-left rounded-lg px-4 py-3 flex items-center justify-between gap-3"
                style={{ background: set ? C.greenSoft : C.surface, border: `1px solid ${set ? C.green : C.border}` }}>
                <div className="min-w-0">
                  <p className="text-sm font-medium truncate">{r.name}</p>
                  <p className="text-xs" style={{ color: C.soft }}>
                    {isCharge ? `demandé ${e.qty} ${r.unit}` : `sorti ${e.qty} ${r.unit}`}
                  </p>
                </div>
                {set ? <span className="text-sm font-bold" style={{ color: C.green }}>{q}</span> : <QrCode size={16} color={C.soft} />}
              </button>
            );
          })}
        </div>

        {expectedOutils.length > 0 && (
          <>
            <div className="mt-5" />
            <SectionTitle icon={Hammer} label="Outillage (sans QR — quantité à saisir)" />
            <div className="flex flex-col gap-2">
              {expectedOutils.map((l) => {
                const o = outilById[l.outilId];
                const q = outilsQty[l.outilId];
                const saisi = q !== undefined;
                const set = (v) => setOutilsQty({ ...outilsQty, [l.outilId]: Math.max(0, v) });
                return (
                  <div key={l.outilId} className="rounded-lg px-4 py-3"
                    style={{ background: saisi ? C.greenSoft : C.surface, border: `1px solid ${saisi ? C.green : C.border}` }}>
                    <div className="flex items-center justify-between gap-3">
                      <div className="min-w-0">
                        <p className="text-sm font-medium truncate">{o ? o.name : 'Outil supprimé'}</p>
                        <p className="text-xs" style={{ color: C.soft }}>
                          {isCharge ? `demandé ${l.qty}` : `sorti ${l.qty}`}
                        </p>
                      </div>
                      <div className="flex items-center gap-2 flex-shrink-0">
                        <button onClick={() => set((q === undefined ? l.qty : q) - 1)}
                          className="rounded-lg text-lg font-bold" style={{ width: 34, height: 34, background: C.steelSoft, color: C.steel }}>−</button>
                        <input type="number" min="0" value={saisi ? q : ''} placeholder={String(l.qty)}
                          onChange={(e) => set(Number(e.target.value))}
                          className="text-center text-sm font-bold outline-none rounded"
                          style={{ width: 52, border: `1px solid ${C.border}`, padding: '6px 2px', background: '#FCFBF9' }} />
                        <button onClick={() => set((q === undefined ? l.qty : q) + 1)}
                          className="rounded-lg text-lg font-bold" style={{ width: 34, height: 34, background: C.steelSoft, color: C.steel }}>+</button>
                      </div>
                    </div>
                  </div>
                );
              })}
            </div>
          </>
        )}
      </div>

      <div className="fixed bottom-0 left-0 right-0 px-5 py-4" style={{ background: C.bg, borderTop: `1px solid ${C.border}` }}>
        <PrimaryButton disabled={done === 0} color={isCharge ? C.accent : C.green} onClick={validate}>
          {isCharge ? 'Valider le chargement' : 'Valider le repli'}{done < total ? ` (${done}/${total})` : ''}
        </PrimaryButton>
        {done < total && done > 0 && (
          <p className="text-[11px] text-center mt-2" style={{ color: C.soft }}>
            Les lignes non validées ne partiront pas / ne rentreront pas en stock.
          </p>
        )}
      </div>

      {pendingEtat && (
        <EtatSheet unit={unitById[pendingEtat]} onClose={() => setPendingEtat(null)}
          onSave={(etat, comment) => {
            setScannedUnits((s) => ({ ...s, [pendingEtat]: { etat, comment } }));
            notify(`${unitById[pendingEtat].name} — ${ETATS[etat].label}`);
            setPendingEtat(null);
          }} />
      )}

      {pendingConso && (
        <QtySheet
          reference={refById[pendingConso]}
          expected={expectedConsos.find((e) => e.refId === pendingConso).qty}
          isCharge={isCharge}
          onClose={() => setPendingConso(null)}
          onSave={(qty) => {
            setConsoQty((s) => ({ ...s, [pendingConso]: qty }));
            notify(`${refById[pendingConso].name} — ${qty} ${isCharge ? 'chargé' : 'rentré'}`);
            setPendingConso(null);
          }} />
      )}
    </div>
  );
}

function EtatSheet({ unit, onClose, onSave }) {
  const [etat, setEtat] = useState(null);
  const [comment, setComment] = useState('');
  const needComment = etat === 'hs';
  const perime = daysUntil(prochaineRevision(unit)) < 0;
  return (
    <Sheet title={`État — ${unit.name}`} onClose={onClose}>
      {perime && (
        <div className="rounded-lg px-3 py-2 mb-3 text-xs" style={{ background: C.redSoft, color: C.red }}>
          Révision dépassée depuis le {frDate(prochaineRevision(unit))} : cette unité partira en quarantaine quel que soit son état.
        </div>
      )}
      <div className="flex gap-2 mb-4">
        {Object.entries(ETATS).map(([key, e]) => {
          const Icon = e.icon, on = etat === key;
          return (
            <button key={key} onClick={() => setEtat(key)}
              className="flex-1 rounded-lg py-3 flex flex-col items-center gap-1 text-xs font-semibold"
              style={{ background: on ? e.soft : '#FCFBF9', border: `2px solid ${on ? e.color : C.border}`, color: on ? e.color : C.soft }}>
              <Icon size={20} />{e.label}
            </button>
          );
        })}
      </div>
      {needComment && (
        <Field label="Commentaire (obligatoire pour un matériel HS)">
          <textarea style={{ ...inputStyle, minHeight: 72, resize: 'vertical' }} value={comment}
            onChange={(e) => setComment(e.target.value)} placeholder="Ex. moteur ne démarre plus, flexible percé…" />
        </Field>
      )}
      {etat === 'hs' && (
        <p className="text-xs mb-3" style={{ color: C.red }}>
          Le matériel part en quarantaine et sort des commandes possibles jusqu'à révision.
        </p>
      )}
      <PrimaryButton disabled={!etat || (needComment && !comment.trim())} color={etat ? ETATS[etat].color : C.accent}
        onClick={() => onSave(etat, comment.trim())}>
        Valider l'état
      </PrimaryButton>
    </Sheet>
  );
}

function QtySheet({ reference: r, expected, isCharge, onClose, onSave }) {
  const [qty, setQty] = useState(expected);
  return (
    <Sheet title={r.name} onClose={onClose}>
      <p className="text-xs mb-3" style={{ color: C.soft }}>
        {isCharge
          ? `Quantité réellement chargée dans le camion (demandé : ${expected} ${r.unit}).`
          : `Quantité qui revient du chantier (sortie : ${expected} ${r.unit}). Le reste est compté comme consommé.`}
      </p>
      <div className="flex items-center gap-3 mb-4">
        <button onClick={() => setQty(Math.max(0, qty - 1))} className="rounded-lg text-xl font-bold" style={{ width: 46, height: 46, background: C.steelSoft, color: C.steel }}>−</button>
        <input type="number" min="0" value={qty} onChange={(e) => setQty(Math.max(0, Number(e.target.value)))}
          className="flex-1 text-center text-2xl font-bold outline-none rounded-lg"
          style={{ border: `1px solid ${C.border}`, padding: 8, background: '#FCFBF9' }} />
        <button onClick={() => setQty(qty + 1)} className="rounded-lg text-xl font-bold" style={{ width: 46, height: 46, background: C.steelSoft, color: C.steel }}>+</button>
      </div>
      <PrimaryButton onClick={() => onSave(qty)}>Valider la quantité</PrimaryButton>
    </Sheet>
  );
}
