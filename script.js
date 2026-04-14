// ══════════════════════════════════════════
//  UTILS
// ══════════════════════════════════════════
function $$(id){return document.getElementById(id)}
function toast(m,d=2400){const t=$$('toast');t.textContent=m;t.classList.add('show');setTimeout(()=>t.classList.remove('show'),d)}
function esc(s){return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')}
function show(id){$$(id).style.display=''}
function hide(id){$$(id).style.display='none'}

function goTab(name,btn){
  document.querySelectorAll('.panel').forEach(p=>p.classList.remove('on'));
  document.querySelectorAll('.tb').forEach(b=>b.classList.remove('on'));
  $$('panel-'+name).classList.add('on');
  if(btn)btn.classList.add('on');
  else document.querySelectorAll('.tb')[name==='dfa'?1:0].classList.add('on');
}
function goToBuilder(){goTab('builder',document.querySelectorAll('.tb')[0])}

// ══════════════════════════════════════════
//  NOTATION MODE  (TAFL vs Programming)
//  TAFL:  + means union (a+b = a|b), no one-or-more
//  Prog:  + means one-or-more (standard regex)
// ══════════════════════════════════════════
let taflMode = true; // default: TAFL (Theory of Computation)

function toggleMode(){
  taflMode = !taflMode;
  updateModeUI();
}

function updateModeUI(){
  const btn = $$('modeBtn');
  const desc = $$('modeDesc');
  const plusSub = $$('plusSub');
  const qBtn = $$('qmarkBtn');
  if(taflMode){
    btn.textContent = '📐 TAFL Mode (Active)';
    btn.style.borderColor = 'var(--g)';
    btn.style.color = 'var(--g2)';
    desc.innerHTML = '<code style="font-family:var(--font-m);color:var(--p2)">+</code> = union (like |) &nbsp;·&nbsp; <code style="font-family:var(--font-m);color:var(--p2)">*</code> = Kleene star &nbsp;·&nbsp; e.g. <code style="font-family:var(--font-m);color:var(--g2)">(a+b)*</code> matches all strings over {a,b}';
    plusSub.textContent = 'union (TAFL)';
    qBtn.style.opacity = '0.4';
    qBtn.title = 'Not available in TAFL mode';
  } else {
    btn.textContent = '💻 Programming Mode (Active)';
    btn.style.borderColor = 'var(--p)';
    btn.style.color = 'var(--p2)';
    desc.innerHTML = '<code style="font-family:var(--font-m);color:var(--p2)">+</code> = one or more &nbsp;·&nbsp; <code style="font-family:var(--font-m);color:var(--a2)">|</code> = union &nbsp;·&nbsp; e.g. <code style="font-family:var(--font-m);color:var(--g2)">a(b|c)+</code>';
    plusSub.textContent = 'one or more';
    qBtn.style.opacity = '1';
    qBtn.title = '';
  }
}


//  Handles: literals, ε, |, concatenation,
//           * (Kleene), + (one-or-more), ? (optional)
//  NO JavaScript RegExp used for matching.
// ══════════════════════════════════════════

// ── NFA state counter ──
let stateId=0;
function newState(){return stateId++}

// NFA node: {id, transitions:{char:[states]}, epsilons:[states]}
function mkState(){return {id:newState(),trans:{},eps:[]}}

// NFA = {start, accept}
// Build NFA from parsed AST node
function nfaFromAST(node){
  stateId=0;
  return buildNFA(node);
}

function buildNFA(node){
  if(node.type==='lit'){
    // Single char
    const s=mkState(),a=mkState();
    (s.trans[node.c]||(s.trans[node.c]=[])).push(a);
    return {start:s,accept:a};
  }
  if(node.type==='eps'){
    const s=mkState(),a=mkState();
    s.eps.push(a);
    return {start:s,accept:a};
  }
  if(node.type==='cat'){
    // Concatenate left then right
    const L=buildNFA(node.left),R=buildNFA(node.right);
    L.accept.eps.push(R.start);
    return {start:L.start,accept:R.accept};
  }
  if(node.type==='alt'){
    // Union: new start → L.start, R.start; L.accept, R.accept → new accept
    const s=mkState(),a=mkState();
    const L=buildNFA(node.left),R=buildNFA(node.right);
    s.eps.push(L.start,R.start);
    L.accept.eps.push(a);
    R.accept.eps.push(a);
    return {start:s,accept:a};
  }
  if(node.type==='star'){
    const s=mkState(),a=mkState();
    const N=buildNFA(node.child);
    s.eps.push(N.start,a);
    N.accept.eps.push(N.start,a);
    return {start:s,accept:a};
  }
  if(node.type==='plus'){
    // aa* equivalent
    const s=mkState(),a=mkState();
    const N=buildNFA(node.child);
    s.eps.push(N.start);
    N.accept.eps.push(N.start,a);
    return {start:s,accept:a};
  }
  if(node.type==='opt'){
    // a|ε
    const s=mkState(),a=mkState();
    const N=buildNFA(node.child);
    s.eps.push(N.start,a);
    N.accept.eps.push(a);
    return {start:s,accept:a};
  }
  throw new Error('Unknown node type: '+node.type);
}

// ε-closure
function epsClosure(states){
  const visited=new Set(states.map(s=>s.id));
  const stack=[...states];
  while(stack.length){
    const cur=stack.pop();
    for(const nxt of cur.eps){
      if(!visited.has(nxt.id)){visited.add(nxt.id);stack.push(nxt);}
    }
  }
  return states.filter((s,_,arr)=>true).concat(
    [...visited].map(id=>stateMap.get(id)).filter(Boolean)
  ).filter((s,i,arr)=>arr.findIndex(x=>x.id===s.id)===i);
}

// We'll maintain a flat stateMap for NFA simulation
let stateMap=new Map();
function collectStates(nfa){
  stateMap=new Map();
  const visited=new Set();
  const stack=[nfa.start];
  while(stack.length){
    const s=stack.pop();
    if(visited.has(s.id))continue;
    visited.add(s.id);
    stateMap.set(s.id,s);
    for(const nxt of s.eps)stack.push(nxt);
    for(const targets of Object.values(s.trans))for(const t of targets)stack.push(t);
  }
}

// NFA simulate: accepts string?
function nfaAccepts(nfa,str){
  collectStates(nfa);
  let cur=epsClosure([nfa.start]);
  for(const ch of str){
    const nxt=[];
    for(const s of cur){
      const targets=s.trans[ch]||[];
      for(const t of targets)nxt.push(t);
    }
    cur=epsClosure(nxt);
    if(!cur.length)return false;
  }
  return cur.some(s=>s.id===nfa.accept.id);
}

// ── PARSER ──────────────────────────────
// Grammar:
//   expr   = term ('|' term)*
//   term   = factor factor*
//   factor = atom ('*' | '+' | '?')*
//   atom   = literal | 'ε' | '(' expr ')'

function parse(input){
  // preprocess: replace ε
  const tokens=[...input.replace(/\s/g,'')];
  let pos=0;

  function peek(){return pos<tokens.length?tokens[pos]:null}
  function consume(c){
    if(peek()!==c)throw new Error('Expected '+c+' but got '+(peek()||'end'));
    return tokens[pos++];
  }
  function next(){return tokens[pos++]}

  function parseExpr(){
    let node=parseTerm();
    // In TAFL mode: both | and + are union operators
    // In Prog mode: only | is union
    while(peek()==='|' || (taflMode && peek()==='+' && pos > 0)){
      pos++;
      const right=parseTerm();
      node={type:'alt',left:node,right};
    }
    return node;
  }

  function parseTerm(){
    // Collect factors, concatenate left to right
    // In TAFL mode, + is a union operator so stop at it (like |)
    let node=null;
    while(peek()!==null && peek()!=='|' && peek()!==')' && !(taflMode && peek()==='+') ){
      const f=parseFactor();
      node=node?{type:'cat',left:node,right:f}:f;
    }
    if(!node)throw new Error('Empty term');
    return node;
  }

  function parseFactor(){
    let node=parseAtom();
    // In TAFL mode: + is NOT a quantifier (it's a union at expr level)
    // In Prog mode: *, +, ? are all quantifiers
    while(peek()==='*' || (!taflMode && (peek()==='+' || peek()==='?'))){
      const op=next();
      if(op==='*')node={type:'star',child:node};
      else if(op==='+')node={type:'plus',child:node};
      else node={type:'opt',child:node};
    }
    // In TAFL mode still allow ? as optional
    if(taflMode && peek()==='?'){
      next();
      node={type:'opt',child:node};
    }
    return node;
  }

  function parseAtom(){
    const c=peek();
    if(c===null)throw new Error('Unexpected end of expression');
    if(c==='('){
      pos++;
      const node=parseExpr();
      consume(')');
      return node;
    }
    if(c==='ε'){pos++;return {type:'eps'}}
    // literal character
    if(/[a-zA-Z0-9\.]/.test(c)){pos++;return {type:'lit',c}}
    throw new Error('Unexpected character: '+c);
  }

  const ast=parseExpr();
  if(pos!==tokens.length)throw new Error('Unexpected character at position '+pos+': '+tokens[pos]);
  return ast;
}

// Compile RE string → NFA (reset stateId first)
function compileRE(re){
  stateId=0;
  const ast=parse(re);
  const nfa=nfaFromAST(ast);
  collectStates(nfa);
  return nfa;
}

function matchesNFA(re,str){
  try{
    stateId=0;
    const ast=parse(re);
    const nfa=buildNFA(ast);
    collectStates(nfa);
    return nfaAccepts(nfa,str);
  }catch{return false;}
}

// ── ALPHABET INFERENCE ──────────────────
function inferAlpha(re){
  const s=new Set();
  // grab literal chars only (not operators)
  for(const c of re){
    if(/[a-zA-Z0-9]/.test(c))s.add(c);
  }
  if(s.size===0){s.add('a');s.add('b');}
  return [...s].sort().slice(0,6);
}

// ── ENUMERATE STRINGS ───────────────────
function enumStrings(alpha,maxLen){
  const result=[''];
  const q=[''];
  while(q.length){
    const s=q.shift();
    if(s.length>=maxLen)continue;
    for(const c of alpha){
      const ns=s+c;
      result.push(ns);
      if(ns.length<maxLen)q.push(ns);
    }
  }
  return result;
}

// ══════════════════════════════════════════
//  DFA via SUBSET CONSTRUCTION
// ══════════════════════════════════════════
function buildDFA(re){
  stateId=0;
  const ast=parse(re);
  const nfa=buildNFA(ast);
  collectStates(nfa);

  const alpha=inferAlpha(re);

  // Each DFA state = sorted set of NFA state ids, as string key
  function closure(nfaStates){
    return epsClosure(nfaStates);
  }
  function stateKey(nfaStates){
    return [...new Set(nfaStates.map(s=>s.id))].sort((a,b)=>a-b).join(',');
  }
  function move(nfaStates,sym){
    const nxt=[];
    for(const s of nfaStates){
      const targets=s.trans[sym]||[];
      for(const t of targets)nxt.push(t);
    }
    return closure(nxt);
  }

  const startSet=closure([nfa.start]);
  const startKey=stateKey(startSet);

  const dfaStates={};  // key → {id, nfaStates, isAccept, trans:{sym:key}}
  let dfaId=0;
  const queue=[{key:startKey,nfaStates:startSet}];
  dfaStates[startKey]={id:dfaId++,nfaStates:startSet,isAccept:startSet.some(s=>s.id===nfa.accept.id),trans:{}};

  while(queue.length){
    const {key,nfaStates}=queue.shift();
    for(const sym of alpha){
      const nxtSet=move(nfaStates,sym);
      if(!nxtSet.length){
        // dead state
        dfaStates[key].trans[sym]='∅';
        continue;
      }
      const nxtKey=stateKey(nxtSet);
      if(!dfaStates[nxtKey]){
        dfaStates[nxtKey]={id:dfaId++,nfaStates:nxtSet,isAccept:nxtSet.some(s=>s.id===nfa.accept.id),trans:{}};
        queue.push({key:nxtKey,nfaStates:nxtSet});
      }
      dfaStates[key].trans[sym]=nxtKey;
    }
  }

  return {states:dfaStates,startKey,alpha,nfaAcceptId:nfa.accept.id};
}

// ══════════════════════════════════════════
//  DFA SVG RENDERER  — overlap-free layout
// ══════════════════════════════════════════
function renderDFASVG(dfa){
  const {states,startKey,alpha}=dfa;
  const stateKeys=Object.keys(states);
  const N=stateKeys.length;
  const SR=30; // state radius
  const MIN_DIST=SR*4; // minimum centre-to-centre distance

  // ── 1. BFS layers from start state ──────
  const layer={};
  const layerNodes=[];
  const visited=new Set();
  let queue=[startKey];
  layer[startKey]=0;
  visited.add(startKey);
  while(queue.length){
    const next=[];
    for(const k of queue){
      const st=states[k];
      for(const tgt of Object.values(st.trans)){
        if(tgt==='∅'||visited.has(tgt))continue;
        visited.add(tgt);layer[tgt]=(layer[k]||0)+1;next.push(tgt);
      }
    }
    queue=next;
  }
  // Unreachable states get their own layer
  stateKeys.forEach(k=>{if(layer[k]===undefined)layer[k]=99;});
  const maxLayer=Math.max(...stateKeys.map(k=>layer[k]));
  for(let L=0;L<=maxLayer;L++)layerNodes.push(stateKeys.filter(k=>layer[k]===L));

  // ── 2. Assign grid positions ─────────────
  const HGAP=Math.max(MIN_DIST, 120); // horizontal gap between layers
  const VGAP=Math.max(MIN_DIST, 100); // vertical gap within layer
  const positions={};
  const PAD=70; // left padding for start arrow

  layerNodes.forEach((nodes,L)=>{
    const x=PAD + L*HGAP + SR;
    nodes.forEach((k,i)=>{
      const totalH=(nodes.length-1)*VGAP;
      const y=SR+60 + i*VGAP - totalH/2 + Math.max(200,(maxLayer+1)*VGAP*0.5);
      positions[k]={x,y};
    });
  });

  // ── 3. Force-repel to remove overlaps ────
  for(let iter=0;iter<80;iter++){
    for(let i=0;i<stateKeys.length;i++){
      for(let j=i+1;j<stateKeys.length;j++){
        const a=positions[stateKeys[i]],b=positions[stateKeys[j]];
        const dx=b.x-a.x,dy=b.y-a.y;
        const dist=Math.sqrt(dx*dx+dy*dy)||1;
        if(dist<MIN_DIST){
          const push=(MIN_DIST-dist)/2+1;
          const ux=dx/dist,uy=dy/dist;
          // Only push vertically within same layer to preserve layering
          if(layer[stateKeys[i]]===layer[stateKeys[j]]){
            a.y-=uy*push; b.y+=uy*push;
          } else {
            a.x-=ux*push*0.3; b.x+=ux*push*0.3;
            a.y-=uy*push*0.5; b.y+=uy*push*0.5;
          }
        }
      }
    }
  }

  // ── 4. Compute canvas bounds ─────────────
  const xs=stateKeys.map(k=>positions[k].x);
  const ys=stateKeys.map(k=>positions[k].y);
  const minX=Math.min(...xs)-SR-PAD;
  const minY=Math.min(...ys)-SR-60;
  const maxX=Math.max(...xs)+SR+40;
  const maxY=Math.max(...ys)+SR+50;
  const W=maxX-minX, H=maxY-minY;

  let svg=`<svg viewBox="${minX} ${minY} ${W} ${H}" xmlns="http://www.w3.org/2000/svg" style="width:100%;max-width:${Math.max(500,W)}px;height:auto;min-height:${Math.max(300,H)}px">
  <defs>
    <marker id="arr" markerWidth="9" markerHeight="9" refX="7" refY="3" orient="auto">
      <path d="M0,0 L9,3 L0,6 Z" fill="#a99af8"/>
    </marker>
    <marker id="arr-g" markerWidth="9" markerHeight="9" refX="7" refY="3" orient="auto">
      <path d="M0,0 L9,3 L0,6 Z" fill="#00e5b0"/>
    </marker>
    <filter id="glow"><feGaussianBlur stdDeviation="2" result="blur"/><feMerge><feMergeNode in="blur"/><feMergeNode in="SourceGraphic"/></feMerge></filter>
  </defs>`;

  // ── 5. Collect transitions ───────────────
  const transMap={};
  for(const [k,st] of Object.entries(states)){
    for(const [sym,tgt] of Object.entries(st.trans)){
      if(tgt==='∅')continue;
      const edge=k+'\u2192'+tgt;
      (transMap[edge]||(transMap[edge]=[])).push(sym);
    }
  }

  // ── 6. Draw edges ────────────────────────
  // Track how many parallel edges exist between pairs to offset labels
  const pairCount={};
  for(const edge of Object.keys(transMap)){
    const sep=edge.indexOf('\u2192');
    const fk=edge.slice(0,sep),tk=edge.slice(sep+1);
    const pair=[fk,tk].sort().join('|');
    pairCount[pair]=(pairCount[pair]||0)+1;
  }

  for(const [edge,syms] of Object.entries(transMap)){
    const sep=edge.indexOf('\u2192');
    const fromKey=edge.slice(0,sep),toKey=edge.slice(sep+1);
    const from=positions[fromKey],to=positions[toKey];
    const label=syms.join(',');

    if(fromKey===toKey){
      // Self-loop — always draw above the node
      const cx=from.x, baseY=from.y-SR;
      const loopH=50, loopW=36;
      svg+=`<path d="M${cx-loopW/2},${baseY} C${cx-loopW},${baseY-loopH} ${cx+loopW},${baseY-loopH} ${cx+loopW/2},${baseY}"
        fill="none" stroke="#a99af8" stroke-width="1.8" marker-end="url(#arr)"/>`;
      svg+=`<rect x="${cx-18}" y="${baseY-loopH-18}" width="36" height="18" rx="4" fill="#1e2330" opacity=".85"/>`;
      svg+=`<text x="${cx}" y="${baseY-loopH-5}" fill="#c9bfff" font-size="12" font-family="IBM Plex Mono,monospace" text-anchor="middle" font-weight="700">${esc(label)}</text>`;
    } else {
      const dx=to.x-from.x,dy=to.y-from.y;
      const dist=Math.sqrt(dx*dx+dy*dy)||1;
      const ux=dx/dist,uy=dy/dist;
      const hasRev=!!transMap[toKey+'\u2192'+fromKey];

      const sx=from.x+ux*SR,sy=from.y+uy*SR;
      const ex=to.x-ux*(SR+6),ey=to.y-uy*(SR+6);

      if(hasRev){
        // Bidirectional: curve both ways
        const nx=-uy,ny=ux;
        const bend=38;
        const cpx=((sx+ex)/2)+nx*bend,cpy=((sy+ey)/2)+ny*bend;
        const lx=sx*0.2+cpx*0.6+ex*0.2,ly=sy*0.2+cpy*0.6+ey*0.2;
        svg+=`<path d="M${sx},${sy} Q${cpx},${cpy} ${ex},${ey}" fill="none" stroke="#a99af8" stroke-width="1.8" marker-end="url(#arr)"/>`;
        const bgw=label.length*8+12;
        svg+=`<rect x="${lx-bgw/2}" y="${ly-14}" width="${bgw}" height="18" rx="4" fill="#1e2330" opacity=".85"/>`;
        svg+=`<text x="${lx}" y="${ly-2}" fill="#c9bfff" font-size="12" font-family="IBM Plex Mono,monospace" text-anchor="middle" font-weight="700">${esc(label)}</text>`;
      } else {
        svg+=`<line x1="${sx}" y1="${sy}" x2="${ex}" y2="${ey}" stroke="#a99af8" stroke-width="1.8" marker-end="url(#arr)"/>`;
        const mx=(sx+ex)/2,my=(sy+ey)/2;
        // Offset label perpendicular to edge
        const nx=-uy,ny=ux;
        const off=16;
        const lx=mx+nx*off,ly=my+ny*off;
        const bgw=label.length*8+12;
        svg+=`<rect x="${lx-bgw/2}" y="${ly-14}" width="${bgw}" height="18" rx="4" fill="#1e2330" opacity=".85"/>`;
        svg+=`<text x="${lx}" y="${ly-2}" fill="#c9bfff" font-size="12" font-family="IBM Plex Mono,monospace" text-anchor="middle" font-weight="700">${esc(label)}</text>`;
      }
    }
  }

  // ── 7. Draw states (on top of edges) ─────
  for(const [k,st] of Object.entries(states)){
    const {x,y}=positions[k];
    const isStart=k===startKey;
    const isAcc=st.isAccept;
    const col=isAcc?(isStart?'#c9bfff':'#ffc55c'):(isStart?'#00e5b0':'#9ba4bc');
    const fillCol=isAcc?'#ffc55c18':(isStart?'#00e5b018':'#1e2330');

    // Shadow/glow for accept states
    if(isAcc){
      svg+=`<circle cx="${x}" cy="${y}" r="${SR+6}" fill="${col}" opacity=".10"/>`;
    }
    svg+=`<circle cx="${x}" cy="${y}" r="${SR}" fill="${fillCol}" stroke="${col}" stroke-width="2.5"/>`;
    if(isAcc){
      // Double circle for accept
      svg+=`<circle cx="${x}" cy="${y}" r="${SR-6}" fill="none" stroke="${col}" stroke-width="1.5"/>`;
    }
    const lbl='q'+st.id;
    svg+=`<text x="${x}" y="${y+5}" fill="${col}" font-size="14" font-weight="800" font-family="IBM Plex Mono,monospace" text-anchor="middle">${esc(lbl)}</text>`;

    // Start arrow from left
    if(isStart){
      const ax=x-SR-8, ax0=x-SR-42;
      svg+=`<line x1="${ax0}" y1="${y}" x2="${ax}" y2="${y}" stroke="#00e5b0" stroke-width="2.2" marker-end="url(#arr-g)"/>`;
      svg+=`<text x="${ax0-4}" y="${y+4}" fill="#00e5b0" font-size="11" font-family="IBM Plex Mono,monospace" text-anchor="end" font-weight="700">start</text>`;
    }
  }

  svg+=`</svg>`;
  return svg;
}

function buildAndShowDFA(){
  const re=lastRE||$$('reIn').value.trim();
  if(!re){toast('Enter a regular expression in the Builder first');return;}

  // Update label
  $$('dfaRELabel').textContent=re;

  let dfa;
  try{
    dfa=buildDFA(re);
  }catch(e){
    $$('dfaSVGWrap').innerHTML=`<div class="dfa-ph" style="color:var(--r2)">Error: ${esc(e.message)}</div>`;
    return;
  }

  const {states,startKey,alpha}=dfa;
  const stateKeys=Object.keys(states);

  if(stateKeys.length>20){
    $$('dfaSVGWrap').innerHTML=`<div class="dfa-ph" style="color:var(--a2)">DFA has ${stateKeys.length} states — too many to visualize clearly. Check the transition table below.</div>`;
  } else {
    $$('dfaSVGWrap').innerHTML=renderDFASVG(dfa);
  }

  // Build transition table
  let tbl=`<table class="dfa-tbl"><thead><tr><th>State</th>`;
  for(const sym of alpha)tbl+=`<th>${esc(sym)}</th>`;
  tbl+=`</tr></thead><tbody>`;

  for(const [k,st] of Object.entries(states)){
    const isStart=k===startKey,isAcc=st.isAccept;
    let label='q'+st.id;
    let cls='';
    if(isStart&&isAcc){label='→* q'+st.id;cls='dfa-state-both';}
    else if(isStart){label='→ q'+st.id;cls='dfa-state-start';}
    else if(isAcc){label='* q'+st.id;cls='dfa-state-acc';}

    tbl+=`<tr><td class="${cls}">${esc(label)}</td>`;
    for(const sym of alpha){
      const tgt=st.trans[sym];
      if(!tgt||tgt==='∅'){
        tbl+=`<td style="color:var(--r2)">∅</td>`;
      } else {
        const tgtSt=states[tgt];
        tbl+=`<td>q${tgtSt.id}${tgtSt.isAccept?' *':''}</td>`;
      }
    }
    tbl+=`</tr>`;
  }
  tbl+=`</tbody></table>`;
  $$('dfaTableWrap').innerHTML=tbl;
  show('dfaTableCard');
  toast(`DFA built: ${stateKeys.length} state(s), alphabet {${alpha.join(',')}}`);
}

// ══════════════════════════════════════════
//  INPUT / PALETTE
// ══════════════════════════════════════════
const CHARS=['a','b','c','d','e','f','0','1'];
function buildCharRow(){
  const row=$$('charRow');
  CHARS.forEach(c=>{
    const b=document.createElement('button');
    b.className='pk ch';b.textContent=c;
    b.onclick=()=>ins(c);
    row.appendChild(b);
  });
}

function ins(s){
  const el=$$('reIn'),st=el.selectionStart,en=el.selectionEnd,v=el.value;
  el.value=v.slice(0,st)+s+v.slice(en);
  el.selectionStart=el.selectionEnd=st+s.length;
  el.focus();onReIn();
}
function insGrp(){
  const el=$$('reIn'),st=el.selectionStart,en=el.selectionEnd,v=el.value;
  const sel=v.slice(st,en);
  const ins2=sel?'('+sel+')':'()';
  el.value=v.slice(0,st)+ins2+v.slice(en);
  el.selectionStart=sel?st:st+1;
  el.selectionEnd=sel?st+ins2.length:st+1;
  el.focus();onReIn();
}
function setRE(v){$$('reIn').value=v;onReIn();$$('reIn').focus()}
function clearRE(){$$('reIn').value='';onReIn();hideErr();clearResults();updatePreview('reIn','rePreview','e.g.  (a+b)*  or  a(b|c)*');}
function clearResults(){hide('outContent');show('outPh');hide('chartWrap');hide('testCard');}
function copyRE(){const v=$$('reIn').value;if(!v){toast('Nothing to copy');return;}navigator.clipboard.writeText(v).then(()=>toast('Copied ✓'))}
function delLast(){
  const el=$$('reIn'),st=el.selectionStart;
  if(!st)return;
  el.value=el.value.slice(0,st-1)+el.value.slice(el.selectionEnd||st);
  el.selectionStart=el.selectionEnd=st-1;
  el.focus();onReIn();
}
function onReKey(e){if(e.key==='Enter')generate()}
function onReIn(){
  validateRE();
  updatePreview('reIn','rePreview','e.g.  (a+b)*  or  a(b|c)*');
}

// ── PRETTY PREVIEW ────────────────────────
// Renders exam-style superscript notation in the preview div behind the input
function reToHTML(re){
  if(!re)return '';
  let html='',i=0;
  const chars=[...re];
  while(i<chars.length){
    const c=chars[i];
    if(c==='('){
      html+=`<span class="rgrp">(</span>`;i++;
    } else if(c===')'){
      let q='';i++;
      while(i<chars.length&&'*+?'.includes(chars[i])){q+=chars[i];i++;}
      html+=`<span class="rgrp">)</span>${qSup(q)}`;
    } else if(c==='|'){
      html+=`<span class="rop"> | </span>`;i++;
    } else if(c==='ε'){
      html+=`<span class="reps">ε</span>`;i++;
    } else if(/[a-zA-Z0-9]/.test(c)){
      let q='';i++;
      while(i<chars.length&&'*+?'.includes(chars[i])){q+=chars[i];i++;}
      html+=`<span class="rlit">${esc(c)}</span>${qSup(q)}`;
    } else {
      html+=esc(c);i++;
    }
  }
  return html;
}
function qSup(q){
  if(!q)return '';
  const sym={'*':'*','+':'+','?':'?'};
  return '<span class="rquant">'+[...q].map(x=>sym[x]||x).join('')+'</span>';
}
function updatePreview(inputId,previewId,placeholder){
  const v=document.getElementById(inputId).value;
  const el=document.getElementById(previewId);
  if(!v){
    el.innerHTML=`<span class="ph">${placeholder}</span>`;
  } else {
    el.innerHTML=reToHTML(v);
  }
}

// ── EQUIVALENCE LIVE ──────────────────────
function onEqIn(){
  updatePreview('eqA','eqPrevA','e.g. (a|b)*');
  updatePreview('eqB','eqPrevB','e.g. (a+b)*');
  liveEqCheck();
}
function liveEqCheck(){
  const A=$$('eqA').value.trim(), B=$$('eqB').value.trim();
  const strip=$$('eqLive');
  if(!A||!B){strip.style.display='none';return;}
  // Quick validity check
  try{stateId=0;parse(A);}catch(e){strip.style.display='block';strip.style.background='#ff4d6a12';strip.style.border='1px solid #ff4d6a40';strip.style.color='var(--r2)';strip.innerHTML='❌ Expression A: '+esc(e.message);return;}
  try{stateId=0;parse(B);}catch(e){strip.style.display='block';strip.style.background='#ff4d6a12';strip.style.border='1px solid #ff4d6a40';strip.style.color='var(--r2)';strip.innerHTML='❌ Expression B: '+esc(e.message);return;}
  // Quick sample check (up to length 5)
  const aSet=new Set([...inferAlpha(A),...inferAlpha(B)]);
  const alpha=[...aSet].slice(0,4);
  const all=enumStrings(alpha,5);
  let nfaA,nfaB;
  try{stateId=0;nfaA=buildNFA(parse(A));collectStates(nfaA);}catch{strip.style.display='none';return;}
  try{stateId=0;nfaB=buildNFA(parse(B));collectStates(nfaB);}catch{strip.style.display='none';return;}
  let diff=null;
  for(const s of all){
    const ma=nfaAccepts(nfaA,s);
    stateId=0;const nb=buildNFA(parse(B));collectStates(nb);
    const mb=nfaAccepts(nb,s);
    stateId=0;const na2=buildNFA(parse(A));collectStates(na2);nfaA=na2;
    if(ma!==mb){diff={s,ma,mb};break;}
  }
  strip.style.display='block';
  if(!diff){
    strip.style.background='#00c89612';strip.style.border='1px solid #00c89640';strip.style.color='var(--g2)';
    strip.innerHTML='✅ Likely equivalent over tested strings (up to length 5) — click Full Check for complete analysis';
  } else {
    strip.style.background='#ff4d6a12';strip.style.border='1px solid #ff4d6a40';strip.style.color='var(--r2)';
    const sw=diff.s===''?'ε':'"'+diff.s+'"';
    strip.innerHTML=`❌ Not equivalent — witness: ${sw} (A: ${diff.ma?'✓':'✗'}, B: ${diff.mb?'✓':'✗'})`;
  }
}

function validateRE(){
  const v=$$('reIn').value.trim();
  if(!v){hideErr();return true;}
  try{stateId=0;parse(v);hideErr();return true;}
  catch(e){showErr('Parse error: '+e.message);return false;}
}
function showErr(m){const e=$$('reErr');e.textContent=m;e.style.display='block'}
function hideErr(){$$('reErr').style.display='none'}

// ══════════════════════════════════════════
//  GENERATE STRINGS — pure NFA approach
// ══════════════════════════════════════════
let lastRE='',lastMax=5;
const history=[];

function slCh(){$$('slV').textContent=$$('lenSl').value}

function generate(){
  const re=$$('reIn').value.trim();
  if(!re){toast('Enter a regular expression first');return;}
  if(!validateRE()){toast('Fix the parse error first');return;}

  const maxLen=parseInt($$('lenSl').value);
  lastRE=re;lastMax=maxLen;

  // Compile NFA once
  let nfa;
  try{stateId=0;nfa=buildNFA(parse(re));collectStates(nfa);}
  catch(e){showErr('Error: '+e.message);return;}

  // Also update DFA tab label
  $$('dfaRELabel').textContent=re;

  const alpha=inferAlpha(re);
  const all=enumStrings(alpha,maxLen);

  // Test each string against NFA
  const matched=[];
  for(const s of all){
    if(nfaAccepts(nfa,s))matched.push(s);
  }

  const byLen={},totByLen={};
  for(let l=0;l<=maxLen;l++){byLen[l]=[];totByLen[l]=0;}
  all.forEach(s=>{const l=s.length;if(l<=maxLen)totByLen[l]++;});
  matched.forEach(s=>{const l=s.length;if(l<=maxLen)byLen[l].push(s);});

  hide('outPh');show('outContent');
  $$('outLbl').textContent='L( '+re+' )';
  $$('outBadge').textContent=matched.length+' strings';

  $$('statRow').innerHTML=`
    <div class="stat"><div class="stat-v">${matched.length}</div><div class="stat-l">Matched</div></div>
    <div class="stat"><div class="stat-v">${all.length}</div><div class="stat-l">Tested</div></div>
    <div class="stat"><div class="stat-v">{${alpha.join(',')}}</div><div class="stat-l">Alphabet</div></div>
    <div class="stat"><div class="stat-v">${maxLen}</div><div class="stat-l">Max Length</div></div>
  `;

  const grps=$$('outGroups');
  grps.innerHTML='';
  if(matched.length===0){
    grps.innerHTML='<div style="color:var(--txt3);font-size:14px;text-align:center;padding:16px 0">No strings matched. Try increasing max length or adjusting the expression.</div>';
  } else {
    for(let l=0;l<=maxLen;l++){
      if(!byLen[l].length)continue;
      const sec=document.createElement('div');
      sec.className='len-group';
      const label=l===0?'ε (empty string)':'length '+l;
      sec.innerHTML=`<div class="len-hd">Strings of ${label}<span class="len-badge">${byLen[l].length}</span></div><div class="str-grid"></div>`;
      grps.appendChild(sec);
      const grid=sec.querySelector('.str-grid');
      byLen[l].forEach(s=>{
        const chip=document.createElement('div');
        chip.className='str-chip'+(s===''?' eps':'');
        chip.textContent=s===''?'ε':s;
        chip.title='Click to test this string';
        chip.onclick=()=>{$$('testIn').value=s;doTestStr(s,nfa);$$('testCard').scrollIntoView({behavior:'smooth',block:'nearest'});};
        grid.appendChild(chip);
      });
    }
  }

  show('chartWrap');
  renderBar(byLen,totByLen,maxLen);
  show('testCard');
  addHist(re,matched.length,maxLen,alpha);
  toast(`Generated ${matched.length} strings from ${all.length} tested`);
}

// ── BAR CHART ──────────────────────────
function renderBar(byLen,tot,maxLen){
  const bc=$$('barChart');bc.innerHTML='';
  let mx=1;
  for(let l=0;l<=maxLen;l++)if(tot[l]>mx)mx=tot[l];
  for(let l=0;l<=maxLen;l++){
    if(tot[l]===0)continue;
    const m=byLen[l].length,t=tot[l];
    const hT=Math.round((t/mx)*96),hM=Math.round((m/mx)*96);
    const col=document.createElement('div');
    col.className='bar-col';
    col.innerHTML=`
      <div class="bar-val">${m}</div>
      <div style="flex:1;position:relative;width:100%;display:flex;align-items:flex-end">
        <div class="bar-fill bg" style="height:${hT}px;width:100%;position:absolute;bottom:0"></div>
        <div class="bar-fill fg" style="height:${hM}px;width:100%;position:absolute;bottom:0"></div>
      </div>
      <div class="bar-lbl">${l===0?'ε':l}</div>`;
    bc.appendChild(col);
  }
}

// ── TEST ───────────────────────────────
let lastNFA=null;
function doTest(){doTestStr($$('testIn').value,null)}
function doTestStr(s,nfa){
  const re=lastRE||$$('reIn').value.trim();
  if(!re){toast('Generate strings first');return;}
  let ok;
  try{
    stateId=0;
    const n=nfa||(()=>{const n2=buildNFA(parse(re));collectStates(n2);return n2;})();
    ok=nfaAccepts(n,s);
  }catch{ok=false;}
  const v=$$('verdict');
  v.className='verdict '+(ok?'match':'nomatch');
  v.querySelector('.vico').textContent=ok?'✅':'❌';
  $$('vtxt').innerHTML=ok
    ?`<strong>"${esc(s)||'ε'}"</strong> is <strong>accepted</strong> by <code style="font-family:var(--font-m);color:var(--p2)">${esc(re)}</code>`
    :`<strong>"${esc(s)||'ε'}"</strong> is <strong>rejected</strong> by <code style="font-family:var(--font-m);color:var(--p2)">${esc(re)}</code>`;
}
function clearTest(){$$('testIn').value='';$$('verdict').className='verdict empty';$$('verdict').querySelector('.vico').textContent='💡';$$('vtxt').textContent='Enter a string and press Test';}

// ── HISTORY ────────────────────────────
function addHist(re,count,maxLen,alpha){
  const idx=history.findIndex(h=>h.re===re);
  if(idx>-1)history.splice(idx,1);
  history.unshift({re,count,maxLen,alpha,ts:new Date()});
  if(history.length>20)history.pop();
  renderHist();
}
function renderHist(){
  const list=$$('histList');
  if(!history.length){list.innerHTML='<div class="hist-empty">No history yet.</div>';return;}
  list.innerHTML='';
  history.forEach(h=>{
    const d=document.createElement('div');
    d.className='hist-item';
    d.innerHTML=`<div><div class="hist-re">${esc(h.re)}</div><div class="hist-meta">Alphabet: {${h.alpha.join(',')}} · ${h.count} strings · max len ${h.maxLen} · ${since(h.ts)}</div></div><span style="color:var(--p2);font-size:18px">→</span>`;
    d.onclick=()=>{
      setRE(h.re);$$('lenSl').value=h.maxLen;slCh();
      goTab('builder',document.querySelectorAll('.tb')[0]);
      generate();
    };
    list.appendChild(d);
  });
}
function since(d){const s=Math.floor((Date.now()-d)/1000);if(s<60)return 'just now';if(s<3600)return Math.floor(s/60)+'m ago';return Math.floor(s/3600)+'h ago';}

// ── EQUIVALENCE ────────────────────────
function loadEqEx(){
  $$('eqA').value='(a|b)*';
  $$('eqB').value='(a+b)*';
  $$('eqRes').className='eq-res';$$('eqRes').style.display='none';
  hide('cmpCard');
  onEqIn();
  toast('Loaded: (a|b)* vs (a+b)* — test equivalence');
}

function checkEq(){
  const A=$$('eqA').value.trim(),B=$$('eqB').value.trim();
  if(!A||!B){toast('Enter both expressions');return;}

  let nfaA,nfaB;
  try{stateId=0;nfaA=buildNFA(parse(A));collectStates(nfaA);}catch(e){toast('Expression A error: '+e.message);return;}
  try{stateId=0;nfaB=buildNFA(parse(B));collectStates(nfaB);}catch(e){toast('Expression B error: '+e.message);return;}

  const aSet=new Set([...inferAlpha(A),...inferAlpha(B)]);
  const alpha=[...aSet].slice(0,5);
  const all=enumStrings(alpha,7);

  const witnesses=[],rows=[];
  let diffs=0;
  for(const s of all){
    const ma=nfaAccepts(nfaA,s);
    stateId=0;nfaB=buildNFA(parse(B));collectStates(nfaB);
    const mb=nfaAccepts(nfaB,s);
    // Rebuild A nfa for next iteration
    stateId=0;nfaA=buildNFA(parse(A));collectStates(nfaA);
    const diff=ma!==mb;
    if(diff){diffs++;witnesses.push({s,ma,mb});}
    if(rows.length<120)rows.push({s,ma,mb,diff});
  }

  const res=$$('eqRes');
  if(diffs===0){
    res.className='eq-res show eq';$$('eqIco').textContent='✅';$$('eqTtl').textContent='Equivalent over tested domain';
    $$('eqBdy').innerHTML=`Both expressions generate the same language over alphabet {${alpha.join(', ')}} for all strings up to length 7.<br><br><strong>${all.length.toLocaleString()}</strong> strings tested · No witness of non-equivalence found.`;
  } else {
    res.className='eq-res show neq';$$('eqIco').textContent='❌';$$('eqTtl').textContent='Not Equivalent — '+diffs+' difference'+(diffs>1?'s':'')+' found';
    const wits=witnesses.slice(0,5).map(w=>`<code>"${esc(w.s||'ε')}"</code>`).join(', ');
    const dir=witnesses[0]?(witnesses[0].ma?'A accepts but B rejects':'B accepts but A rejects'):'';
    $$('eqBdy').innerHTML=`Found <strong>${diffs}</strong> string${diffs>1?'s':''} where languages differ.<br>Example witnesses: ${wits}<br>First difference: ${dir}`;
  }

  const sorted=[...rows.filter(r=>r.diff),...rows.filter(r=>!r.diff&&r.ma).slice(0,40),...rows.filter(r=>!r.diff&&!r.ma).slice(0,10)];
  const tbody=$$('cmpBody');tbody.innerHTML='';
  sorted.slice(0,80).forEach(({s,ma,mb,diff})=>{
    const tr=document.createElement('tr');
    if(diff)tr.className='diff';
    const verdict=diff?(ma?'A only':'B only'):'Both agree';
    tr.innerHTML=`<td>${s===''?'<em>ε</em>':esc(s)}</td><td class="${ma?'tag-y':'tag-n'}">${ma?'✓':'✗'}</td><td class="${mb?'tag-y':'tag-n'}">${mb?'✓':'✗'}</td><td>${verdict}</td>`;
    tbody.appendChild(tr);
  });
  show('cmpCard');
}
function clearEq(){$$('eqA').value='';$$('eqB').value='';$$('eqRes').className='eq-res';$$('eqRes').style.display='none';hide('cmpCard');updatePreview('eqA','eqPrevA','e.g. (a|b)*');updatePreview('eqB','eqPrevB','e.g. (a+b)*');$$('eqLive').style.display='none';}

// ── REFERENCE ──────────────────────────
const REF=[
  {sym:'a',name:'Literal',desc:'Matches the exact character "a". Any letter or digit.',ex:'a → matches only "a"'},
  {sym:'*',name:'Kleene Star',desc:'Zero or more repetitions of the preceding element.',ex:'a* → ε, a, aa, aaa, …'},
  {sym:'+',name:'Union (TAFL) / One-or-More (Prog)',desc:'In TAFL mode: a+b means a OR b — same as a|b. In Programming mode: a+ means one or more a\'s (equivalent to aa*).',ex:'TAFL: (a+b)* → all strings over {a,b} | Prog: a+ → a, aa, aaa, …'},
  {sym:'?',name:'Optional',desc:'Zero or one occurrence of the preceding element.',ex:'ab? → a, ab'},
  {sym:'|',name:'Union / Alternation',desc:'Matches either the left or right sub-expression.',ex:'a|b → a or b'},
  {sym:'( )',name:'Grouping',desc:'Groups sub-expressions. Operators apply to the whole group.',ex:'(ab)* → ε, ab, abab, …'},
  {sym:'ε',name:'Epsilon',desc:'The empty string — a match of zero characters.',ex:'(a|ε) → ε or a'},
  {sym:'(a+b)*',name:'Union + Kleene (TAFL)',desc:'In TAFL mode, + is union: (a+b)* means zero or more of (a or b) — every string over {a,b}. Same as (a|b)*.',ex:'(a+b)* → ε, a, b, aa, ab, ba, bb, …'},
  {sym:'a|b*',name:'Precedence',desc:'* and + bind tighter than concatenation, which binds tighter than |. Use ( ) to override.',ex:'a|b* means a | (b*), not (a|b)*'},
];
function buildRef(){
  const g=$$('refGrid');
  REF.forEach(r=>{
    const d=document.createElement('div');
    d.className='ref-item';
    d.innerHTML=`<div class="ref-sym">${esc(r.sym)}</div><div class="ref-name">${r.name}</div><div class="ref-desc">${r.desc}</div><div class="ref-ex">${esc(r.ex)}</div>`;
    g.appendChild(d);
  });
}

// ── INIT ────────────────────────────────
buildCharRow();
buildRef();
updateModeUI();
