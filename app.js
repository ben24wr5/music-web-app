'use strict';
const $=s=>document.querySelector(s), esc=s=>String(s??'').replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const fmt=t=>!isFinite(t)||t<=0?'0:00':Math.floor(t/60)+':'+String(Math.floor(t%60)).padStart(2,'0');
const uid=()=>Math.random().toString(36).slice(2)+Date.now().toString(36);
const THEMES={Purple:'#a463f2',Blue:'#0a84ff',Violet:'#8b5cf6',Pink:'#ff375f',Green:'#30d158',Orange:'#ff9f0a',Teal:'#40c8e0',Red:'#ff453a'};
const BANDS=[32,64,125,250,500,1000,2000,4000,8000,16000];
const PRESET_STATIONS=[{id:'s1',name:'SomaFM Groove Salad',url:'https://ice1.somafm.com/groovesalad-128-mp3'},{id:'s2',name:'SomaFM Drone Zone',url:'https://ice1.somafm.com/dronezone-128-mp3'},{id:'s3',name:'Radio Paradise',url:'https://stream.radioparadise.com/mp3-128'}];

// ---------- persistence ----------
let S=Object.assign({songs:[],playlists:[],recent:[],stations:PRESET_STATIONS,podcasts:[],theme:'Purple',dark:true,eq:BANDS.map(()=>0),vol:.8},JSON.parse(localStorage.getItem('musicapp')||'{}'));
const save=()=>localStorage.setItem('musicapp',JSON.stringify(S));
let dbp=new Promise((res,rej)=>{const r=indexedDB.open('musicapp',1);r.onupgradeneeded=()=>r.result.createObjectStore('files');r.onsuccess=()=>res(r.result);r.onerror=()=>rej(r.error)});
const idb=(mode,fn)=>dbp.then(db=>new Promise((res,rej)=>{const tx=db.transaction('files',mode),st=tx.objectStore('files'),r=fn(st);tx.oncomplete=()=>res(r&&r.result);tx.onerror=()=>rej(tx.error)}));
const putBlob=(k,b)=>idb('readwrite',s=>s.put(b,k)), getBlob=k=>idb('readonly',s=>s.get(k)), delBlob=k=>idb('readwrite',s=>s.delete(k));

// ---------- audio graph ----------
const audio=$('#audio'), stream=new Audio();
let ctx,src,filters,analyser,karaokeNodes,vocalCut=false;
function initAudio(){ if(ctx) return; ctx=new (window.AudioContext||window.webkitAudioContext)();
 src=ctx.createMediaElementSource(audio);
 filters=BANDS.map((f,i)=>{const b=ctx.createBiquadFilter();b.type=i==0?'lowshelf':i==9?'highshelf':'peaking';b.frequency.value=f;b.Q.value=1;b.gain.value=S.eq[i];return b});
 analyser=ctx.createAnalyser();analyser.fftSize=128;
 const sp=ctx.createChannelSplitter(2),inv=ctx.createGain(),mix=ctx.createGain();inv.gain.value=-1;sp.connect(mix,0);sp.connect(inv,1);inv.connect(mix);
 karaokeNodes={sp,mix};route(); }
function route(){ if(!ctx)return; src.disconnect();filters.forEach(f=>f.disconnect());karaokeNodes.mix.disconnect();
 let n=src; filters.forEach(f=>{n.connect(f);n=f});
 if(vocalCut){n.connect(karaokeNodes.sp);karaokeNodes.mix.connect(analyser)} else n.connect(analyser);
 analyser.disconnect();analyser.connect(ctx.destination); }

// ---------- state ----------
let speed=1,hist=['songs'],hpos=0,thumbs={};
let queue=[],cur=null,shuffle=false,repeat='off',lyrics=[],view='songs',search='',objURL=null,artURL=null;
const song=id=>S.songs.find(s=>s.id==id);
function smart(r){const a=[...S.songs];return r=='most'?a.filter(s=>s.plays).sort((x,y)=>y.plays-x.plays).slice(0,25):r=='added'?a.sort((x,y)=>y.added-x.added).slice(0,25):r=='never'?a.filter(s=>!s.plays):a.filter(s=>s.fav)}

// ---------- metadata (minimal ID3v2 reader: title/artist/album/picture/lyrics) ----------
async function readTags(file){const t={};try{const b=new Uint8Array(await file.slice(0,Math.min(file.size,4e6)).arrayBuffer());
 if(b[0]!=73||b[1]!=68||b[2]!=51)return t;const v=b[3],size=(b[6]<<21)|(b[7]<<14)|(b[8]<<7)|b[9];let p=10;
 const dec=(arr,enc)=>{try{return new TextDecoder(enc==1?'utf-16':enc==2?'utf-16be':enc==3?'utf-8':'latin1').decode(arr).replace(/\0/g,'').trim()}catch{return''}};
 while(p<size+10&&p+10<b.length){const id=String.fromCharCode(...b.slice(p,p+4));if(!/^[A-Z0-9]{4}$/.test(id))break;
  const fs=v==4?(b[p+4]<<21)|(b[p+5]<<14)|(b[p+6]<<7)|b[p+7]:(b[p+4]<<24)|(b[p+5]<<16)|(b[p+6]<<8)|b[p+7];const d=b.slice(p+10,p+10+fs);
  if(id=='TIT2')t.title=dec(d.slice(1),d[0]);if(id=='TPE1')t.artist=dec(d.slice(1),d[0]);if(id=='TALB')t.album=dec(d.slice(1),d[0]);
  if(id=='USLT'){let q=4;const w=d[0]==1||d[0]==2;while(q<d.length&&!(d[q]==0&&(!w||d[q+1]==0)))q+=w?2:1;t.lyrics=dec(d.slice(q+(w?2:1)),d[0])}
  if(id=='APIC'&&!t.pic){let q=1;while(d[q])q++;const mime=dec(d.slice(1,q),0)||'image/jpeg';q+=2;const w=d[0]==1||d[0]==2;while(q<d.length&&!(d[q]==0&&(!w||d[q+1]==0)))q+=w?2:1;q+=w?2:1;t.pic=new Blob([d.slice(q)],{type:mime})}
  p+=10+fs}}catch(e){}return t}

// ---------- import ----------
async function importFiles(list){const files=[...list],lrcs={};
 for(const f of files) if(/\.lrc$/i.test(f.name)) lrcs[f.name.replace(/\.lrc$/i,'').toLowerCase()]=await f.text();
 let n=0; for(const f of files){ if(!(/^audio\//.test(f.type)||/\.(mp3|m4a|aac|wav|ogg|flac|opus|webm)$/i.test(f.name)))continue;
  const base=f.name.replace(/\.[^.]+$/,''); if(S.songs.some(s=>s.file==f.name&&s.size==f.size))continue;
  const tg=await readTags(f),id=uid(); await putBlob(id,f); if(tg.pic) await putBlob(id+':art',tg.pic);
  const dur=await new Promise(r=>{const a=new Audio();a.preload='metadata';a.onloadedmetadata=()=>{r(a.duration);URL.revokeObjectURL(a.src)};a.onerror=()=>r(0);a.src=URL.createObjectURL(f)});
  S.songs.push({id,file:f.name,size:f.size,title:tg.title||base,artist:tg.artist||'Unknown Artist',album:tg.album||'Unknown Album',dur,plays:0,fav:false,added:Date.now(),last:null,art:!!tg.pic,lyrics:lrcs[base.toLowerCase()]||tg.lyrics||''});n++}
 save();render();if(n)toast(`Imported ${n} song${n>1?'s':''}`)}
$('#folder').onchange=e=>importFiles(e.target.files);$('#files').onchange=e=>importFiles(e.target.files);
async function walk(entry,out){if(entry.isFile)out.push(await new Promise(r=>entry.file(r)));else if(entry.isDirectory){const rd=entry.createReader();let ents;do{ents=await new Promise(r=>rd.readEntries(r));for(const e of ents)await walk(e,out)}while(ents.length)}}
let dragN=0;document.addEventListener('dragenter',e=>{e.preventDefault();dragN++;$('#drop').classList.add('show')});
document.addEventListener('dragleave',()=>{if(--dragN<=0){dragN=0;$('#drop').classList.remove('show')}});
document.addEventListener('dragover',e=>e.preventDefault());
document.addEventListener('drop',async e=>{e.preventDefault();dragN=0;$('#drop').classList.remove('show');const out=[];
 for(const it of e.dataTransfer.items){const en=it.webkitGetAsEntry&&it.webkitGetAsEntry();if(en)await walk(en,out);else if(it.getAsFile())out.push(it.getAsFile())}importFiles(out)});

// ---------- playback ----------
async function play(s,list){ if(list){queue=shuffle?[...list].sort(()=>Math.random()-.5):[...list];if(shuffle){const i=queue.indexOf(s);[queue[0],queue[i]]=[queue[i],queue[0]]}}
 initAudio();ctx.resume();audio.pause();stream.pause();cur=s;
 if(s.stream){stream.src=s.url;stream.volume=S.vol;stream.playbackRate=speed;stream.play().catch(e=>toast('Stream failed: '+e.message));lyrics=[];setArt(null)}
 else{const b=await getBlob(s.id);if(!b)return toast('File missing');if(objURL)URL.revokeObjectURL(objURL);objURL=URL.createObjectURL(b);audio.src=objURL;audio.playbackRate=speed;await audio.play().catch(()=>{});
  s.plays=(s.plays||0)+1;s.last=Date.now();S.recent=[s.id,...S.recent.filter(x=>x!=s.id)].slice(0,50);save();
  lyrics=parseLRC(s.lyrics||'');setArt(s.art?await getBlob(s.id+':art'):null)}
 updateBar();mediaSession();notify(s);render()}
const media=()=>cur&&cur.stream?stream:audio;
function toggle(){if(!cur){const l=visibleSongs();if(l.length)play(l[0],l);return}const m=media();if(m.paused){ctx&&ctx.resume();m.play()}else m.pause();updateBar()}
function next(){if(!cur)return;const i=queue.findIndex(x=>x.id==cur.id);if(i+1<queue.length)play(queue[i+1]);else if(repeat=='all'&&queue.length)play(queue[0]);else{media().pause();updateBar()}}
function prev(){if(!cur)return;if(media().currentTime>3){media().currentTime=0;return}const i=queue.findIndex(x=>x.id==cur.id);if(i>0)play(queue[i-1])}
audio.onended=()=>repeat=='one'?play(cur):next();
[audio,stream].forEach(m=>{m.onplay=m.onpause=updateBar});
function setArt(b){if(artURL)URL.revokeObjectURL(artURL);artURL=b?URL.createObjectURL(b):null;if(artURL)$('#art').src=artURL;else $('#art').removeAttribute('src')}
function updateBar(){const m=media(),p=cur&&!m.paused;$('#play use').setAttribute('href',p?'#i-pause':'#i-play');document.querySelector('#float [data-a=play]').textContent=p?'⏸':'▶';
 $('#title').textContent=cur?cur.title:'Not Playing';$('#artist').textContent=cur?(cur.artist||'').toUpperCase():'Add some music to get started';$('#ftitle').textContent=cur?cur.title:'Not Playing';
 $('#favBtn').textContent=cur&&cur.fav?'★ Unfavourite Song':'☆ Favourite Song';$('#shuf').classList.toggle('on',shuffle);$('#rep').classList.toggle('on',repeat!='off');$('#rep').classList.toggle('one',repeat=='one');
 document.querySelectorAll('.anim').forEach(x=>x.classList.toggle('paused',!p));document.title=cur?`${p?'▶ ':''}${cur.title} — Music`:'Music'}
setInterval(()=>{const m=media();$('#cur').textContent=fmt(m.currentTime);$('#dur').textContent=fmt(m.duration);if(isFinite(m.duration)&&m.duration)$('#seek').value=m.currentTime/m.duration*1000;
 if('mediaSession'in navigator&&isFinite(m.duration)&&m.duration)try{navigator.mediaSession.setPositionState({duration:m.duration,position:Math.min(m.currentTime,m.duration),playbackRate:m.playbackRate})}catch{}
 highlightLyric();npLyrics();document.querySelectorAll('input[type=range]').forEach(r=>{if(!r.closest('.eq'))r.style.setProperty('--p',(r.value-r.min)/(r.max-r.min)*100+'%')})},250);
$('#seek').oninput=e=>{const m=media();if(isFinite(m.duration))m.currentTime=e.target.value/1000*m.duration};
$('#vol').value=S.vol;audio.volume=S.vol;$('#vol').oninput=e=>{S.vol=+e.target.value;audio.volume=stream.volume=S.vol;save()};
$('#speed').onclick=()=>{const L=[0.5,0.75,1,1.25,1.5,2];speed=L[(L.indexOf(speed)+1)%L.length];audio.playbackRate=stream.playbackRate=speed;$('#speed').textContent=speed.toFixed(speed%0.5?2:1)+'x'};
$('#play').onclick=toggle;$('#next').onclick=next;$('#prev').onclick=prev;
$('#shuf').onclick=()=>{shuffle=!shuffle;updateBar()};$('#rep').onclick=()=>{repeat={off:'all',all:'one',one:'off'}[repeat];updateBar()};
$('#favBtn').onclick=()=>{if(cur&&!cur.stream){cur.fav=!cur.fav;save();updateBar();render()}};
document.addEventListener('keydown',e=>{if(e.target.tagName=='INPUT')return;if(e.code=='Space'){e.preventDefault();toggle()}if(e.code=='ArrowRight'&&e.metaKey)next();if(e.code=='ArrowLeft'&&e.metaKey)prev()});

// ---------- media session / notifications / share ----------
function mediaSession(){if(!('mediaSession'in navigator)||!cur)return;navigator.mediaSession.metadata=new MediaMetadata({title:cur.title,artist:cur.artist,album:cur.album||'',artwork:artURL?[{src:artURL}]:[]});
 [['play',toggle],['pause',toggle],['nexttrack',next],['previoustrack',prev]].forEach(([a,f])=>{try{navigator.mediaSession.setActionHandler(a,f)}catch{}})}
function notify(s){if(!('Notification'in window))return;const go=()=>document.hidden&&new Notification('Now Playing',{body:`${s.title} — ${s.artist}`,icon:artURL||undefined,silent:true});
 if(Notification.permission=='granted')go();else if(Notification.permission=='default')Notification.requestPermission()}
async function share(s){const text=`🎵 Listening to ${s.title} — ${s.artist}`;try{if(navigator.share){const b=!s.stream&&await getBlob(s.id),f=b&&new File([b],s.file,{type:b.type});
 if(f&&navigator.canShare&&navigator.canShare({files:[f]}))await navigator.share({title:s.title,text,files:[f]});else await navigator.share({title:s.title,text,url:s.url});}
 else{await navigator.clipboard.writeText(text+(s.url?' '+s.url:''));toast('Copied to clipboard')}}catch(e){if(e.name!='AbortError')toast('Share unavailable')}}
$('#shareBtn').onclick=()=>cur&&share(cur);

// ---------- visualiser ----------
const vis=$('#vis'),vc=vis.getContext('2d');let vt=0;
(function draw(){requestAnimationFrame(draw);const W=vis.width=vis.clientWidth*2,H=vis.height=112;vc.clearRect(0,0,W,H);const n=44;let d=new Uint8Array(64),on=false;vt+=.05;
 if(analyser&&!audio.paused){analyser.getByteFrequencyData(d);on=true}else if(cur&&cur.stream&&!stream.paused){on=true;d=d.map((_,i)=>110+90*Math.sin(vt*3+i*.7)*Math.cos(vt+i*.3))}
 const cs=getComputedStyle(document.body),g=vc.createLinearGradient(0,0,W,0);g.addColorStop(0,cs.getPropertyValue('--acc').trim());g.addColorStop(.55,'#e0609a');g.addColorStop(1,cs.getPropertyValue('--acc2').trim()||'#ff9f43');vc.fillStyle=g;
 const w=W/n;for(let i=0;i<n;i++){const env=Math.sin(Math.PI*(i+.5)/n);const v=on?(d[Math.floor(i/n*40)]/255)*(.5+.5*env):.04+.03*Math.sin(vt+i*.5)*env;const h=Math.max(4,v*H*.95);vc.beginPath();vc.roundRect(i*w+w*.3,(H-h)/2,w*.4,h,w*.2);vc.fill()}})();

// ---------- lyrics ----------
function parseLRC(t){const out=[];t.split(/\r?\n/).forEach(l=>{const m=[...l.matchAll(/\[(\d+):(\d+(?:\.\d+)?)\]/g)],txt=l.replace(/\[[^\]]*\]/g,'').trim();
 if(m.length)m.forEach(x=>out.push({t:+x[1]*60+ +x[2],txt}));else if(txt&&!/^\[/.test(l))out.push({t:-1,txt})});return out.sort((a,b)=>a.t-b.t)}
function curLyric(){const t=media().currentTime;let i=-1;lyrics.forEach((l,k)=>{if(l.t>=0&&l.t<=t)i=k});return i}
let lastLyr=-2;function highlightLyric(){const box=$('.lyr');if(!box)return;const i=curLyric();if(i==lastLyr)return;lastLyr=i;
 box.querySelectorAll('p').forEach((p,k)=>p.classList.toggle('cur',k==i));const c=box.querySelector('p.cur');c&&c.scrollIntoView({block:'center',behavior:'smooth'})}
function lyricsModal(kar){lastLyr=-2;modal(`<div style="display:flex;justify-content:space-between;align-items:center"><h2>${kar?'🎤 Karaoke':'Lyrics'}</h2><span>${kar?`<label><input type="checkbox" id="vc" ${vocalCut?'checked':''}> Vocal reduction</label> `:''}<button onclick="closeModal()">Close</button></span></div>
 <div class="lyr" style="max-height:${kar?400:420}px;overflow:auto">${lyrics.length?lyrics.map(l=>`<p>${esc(l.txt)}</p>`).join(''):'<p style="text-align:center;margin-top:60px">No lyrics found.<br>Import a .lrc file with the same name as the song (or use songs with embedded lyrics).</p>'}</div>`,kar?'kar':'');
 const v=$('#vc');if(v)v.onchange=()=>{vocalCut=v.checked;initAudio();route()}}
$('#lyrBtn').onclick=()=>lyricsModal(false);$('#karBtn').onclick=()=>lyricsModal(true);

// ---------- EQ ----------
$('#eqBtn').onclick=()=>{modal(`<h2>Equaliser</h2><div class="eq">${BANDS.map((f,i)=>`<div><span id="g${i}">${S.eq[i]}</span><input type="range" min="-12" max="12" step="1" value="${S.eq[i]}" data-i="${i}"><span>${f>=1000?f/1000+'k':f}</span></div>`).join('')}</div>
 <div style="display:flex;gap:8px"><button data-p="flat">Flat</button><button data-p="bass">Bass Boost</button><button data-p="vocal">Vocal</button><button data-p="treble">Treble</button><span style="flex:1"></span><button onclick="closeModal()">Done</button></div>`);
 const set=(i,g)=>{S.eq[i]=g;if(filters)filters[i].gain.value=g;$('#g'+i).textContent=g;document.querySelector(`.eq input[data-i="${i}"]`).value=g};
 document.querySelectorAll('.eq input').forEach(r=>r.oninput=()=>{set(+r.dataset.i,+r.value);save()});
 const P={flat:i=>0,bass:i=>i<3?8:i<5?3:0,vocal:i=>i>=4&&i<=6?5:-1,treble:i=>i>6?7:0};
 document.querySelectorAll('[data-p]').forEach(b=>b.onclick=()=>{BANDS.forEach((_,i)=>set(i,P[b.dataset.p](i)));save()})};

// ---------- mini / floating controls ----------
$('#miniBtn').onclick=async()=>{ if('documentPictureInPicture'in window){try{const w=await documentPictureInPicture.requestWindow({width:320,height:90});
   [...document.styleSheets].forEach(s=>{try{const st=w.document.createElement('style');st.textContent=[...s.cssRules].map(r=>r.cssText).join('');w.document.head.append(st)}catch{}});
   w.document.body.className='dark';w.document.body.style.cssText='display:flex;align-items:center;justify-content:center';const f=$('#float');f.classList.remove('hidden');f.style.position='static';w.document.body.append(f);
   w.addEventListener('pagehide',()=>{f.style.position='';f.classList.add('hidden');document.body.append(f)});return}catch(e){}}
 $('#float').classList.toggle('hidden')};
$('#float').onclick=e=>{const a=e.target.dataset.a;if(a=='play')toggle();if(a=='next')next();if(a=='prev')prev();if(a=='close')$('#float').classList.add('hidden')};

// ---------- modal / ctx / toast ----------
function modal(html,cls=''){$('#mcard').className='card '+cls;$('#mcard').innerHTML=html;$('#modal').classList.remove('hidden')}
function closeModal(){$('#modal').classList.add('hidden')}window.closeModal=closeModal;$('#modal').onclick=e=>{if(e.target.id=='modal')closeModal()};
function toast(m){const t=document.createElement('div');t.textContent=m;t.style.cssText='position:fixed;bottom:90px;left:50%;transform:translateX(-50%);background:#000c;color:#fff;padding:8px 16px;border-radius:8px;z-index:30';document.body.append(t);setTimeout(()=>t.remove(),2500)}
function ctxMenu(e,items){e.preventDefault();$('#ctx')?.remove();const m=document.createElement('div');m.id='ctx';m.style.left=e.clientX+'px';m.style.top=e.clientY+'px';
 items.forEach(([l,f])=>{const d=document.createElement('div');d.textContent=l;d.onclick=()=>{m.remove();f()};m.append(d)});document.body.append(m);setTimeout(()=>document.addEventListener('click',()=>m.remove(),{once:true}))}

// ---------- views ----------
function visibleSongs(){let l;const [k,a]=view.split(':');
 l=k=='songs'?S.songs:k=='fav'?smart('fav'):k=='recent'?S.recent.map(song).filter(Boolean):k=='queue'?queue:k=='smart'?smart(a):k=='pl'?(S.playlists.find(p=>p.id==a)?.songs||[]).map(song).filter(Boolean):[];
 return search&&k!='queue'?l.filter(s=>`${s.title} ${s.artist} ${s.album}`.toLowerCase().includes(search.toLowerCase())):l}
const TITLES={songs:'Songs',playlists:'Playlists',smarts:'Smart Playlists',fav:'Favourites',recent:'Recently Played',queue:'Up Next','smart:most':'Most Played','smart:added':'Recently Added','smart:never':'Never Played'};
function go(v,push=true){view=v;if(push){hist=hist.slice(0,hpos+1);hist.push(v);hpos=hist.length-1}render()}
async function thumb(s){if(!s.art)return null;if(!(s.id in thumbs)){thumbs[s.id]=null;const b=await getBlob(s.id+':art');if(b){thumbs[s.id]=URL.createObjectURL(b);render()}}return thumbs[s.id]}
const star=s=>`<svg class="star ${s.fav?'on':''}"><use href="#i-star"/></svg>`;
function render(){const v=$('#view'),[k,a]=view.split(':');
 document.querySelectorAll('#side a').forEach(x=>x.classList.toggle('on',x.dataset.v==view||(x.dataset.v=='playlists'&&k=='pl')||(x.dataset.v=='smarts'&&k=='smart')));
 $('#pls').innerHTML=S.playlists.map(p=>`<a data-v="pl:${p.id}" class="${view=='pl:'+p.id?'on':''}">♪ ${esc(p.name)}</a>`).join('');
 sideStats();
 if(k=='stats')return renderStats(v);if(k=='radio')return renderRadio(v);if(k=='podcasts')return renderPods(v);
 if(k=='playlists'){v.innerHTML=`<h1>Playlists <button id="np2">+ New Playlist</button></h1><div class="tiles">${S.playlists.map(p=>`<div class="tile" data-g="pl:${p.id}"><div class="ph2">♪</div><b>${esc(p.name)}</b><span>${p.songs.length} songs</span></div>`).join('')||'<p style="color:var(--mut)">No playlists yet. Create one, then right-click songs to add them.</p>'}</div>`;
  $('#np2').onclick=newPlaylist;v.querySelectorAll('[data-g]').forEach(t=>t.onclick=()=>go(t.dataset.g));return}
 if(k=='smarts'){v.innerHTML=`<h1>Smart Playlists</h1><div class="tiles">${['most','added','never','fav'].map(r=>`<div class="tile" data-g="${r=='fav'?'fav':'smart:'+r}"><div class="ph2">⚙︎</div><b>${TITLES[r=='fav'?'fav':'smart:'+r]}</b><span>${smart(r).length} songs · auto-updating</span></div>`).join('')}</div>`;
  v.querySelectorAll('[data-g]').forEach(t=>t.onclick=()=>go(t.dataset.g));return}
 const l=visibleSongs(),pl=k=='pl'&&S.playlists.find(p=>p.id==a),title=pl?pl.name:TITLES[view];
 const filt=['songs','fav','smart:added','smart:most','recent'].includes(view)?`<select class="filter" id="filt">${[['songs','All Songs'],['fav','Favourites'],['smart:added','Recently Added'],['smart:most','Most Played'],['recent','Recently Played']].map(([x,y])=>`<option value="${x}" ${x==view?'selected':''}>${y}</option>`).join('')}</select>`:'';
 const playing=cur&&!media().paused;
 v.innerHTML=`<h1>${esc(title)}${pl?` <button id="renPl">Rename</button> <button id="delPl">Delete</button>`:''}</h1>${filt}`+
 (l.length?`<table><tr><th style="padding-left:52px">TITLE</th><th>ARTIST</th><th>ALBUM</th><th>TIME</th><th></th></tr>${l.map(s=>{const th=thumbs[s.id]||(thumb(s),null);return `<tr class="song ${cur&&cur.id==s.id?'playing':''}" data-id="${s.id}"><td class="t"><div class="tc">${cur&&cur.id==s.id?`<div class="anim ${playing?'':'paused'}"><i></i><i></i><i></i><i></i><i></i></div>`:th?`<img class="thumb" src="${th}">`:`<div class="ph2"><svg><use href="#i-music"/></svg></div>`}<span>${esc(s.title)}</span></div></td><td>${esc(s.artist)}</td><td>${esc(s.album)}</td><td>${fmt(s.dur)}</td><td class="fav" style="width:34px">${star(s)}</td></tr>`}).join('')}</table>`
 :S.songs.length?`<p style="color:var(--mut);margin:20px 4px">Nothing here yet.</p>`:`<div class="empty"><div class="big"><svg><use href="#i-music"/></svg></div><h2>Your library is empty</h2><div>Drag songs here or Import Folder</div><button class="pbtn" id="impE">Import Folder</button></div>`);
 if($('#filt'))$('#filt').onchange=e=>go(e.target.value);if($('#impE'))$('#impE').onclick=()=>$('#folder').click();
 v.querySelectorAll('tr.song').forEach(r=>{const s=queue.find(x=>x.id==r.dataset.id)||song(r.dataset.id);
  r.ondblclick=()=>play(s,l);r.querySelector('.fav').onclick=()=>{s.fav=!s.fav;save();render();updateBar()};
  r.oncontextmenu=e=>ctxMenu(e,[['Play',()=>play(s,l)],['Play Next',()=>{const i=cur?queue.findIndex(x=>x.id==cur.id):-1;queue.splice(i+1,0,s)}],['Add to Queue',()=>queue.push(s)],
   [s.fav?'Unfavourite':'Favourite',()=>{s.fav=!s.fav;save();render()}],...S.playlists.map(p=>['Add to '+p.name,()=>{p.songs.push(s.id);save()}]),
   ...(pl?[['Remove from Playlist',()=>{pl.songs=pl.songs.filter(x=>x!=s.id);save();render()}]]:[]),['Share…',()=>share(s)],
   ...(k=='songs'?[['Delete from Library',async()=>{S.songs=S.songs.filter(x=>x.id!=s.id);S.playlists.forEach(p=>p.songs=p.songs.filter(x=>x!=s.id));S.recent=S.recent.filter(x=>x!=s.id);await delBlob(s.id);await delBlob(s.id+':art');save();render()}]]:[])])});
 if(pl){$('#renPl').onclick=()=>{const n=prompt('Playlist name',pl.name);if(n){pl.name=n;save();render()}};$('#delPl').onclick=()=>{S.playlists=S.playlists.filter(p=>p!=pl);go('playlists')}}}
function sideStats(){const n=S.songs.length,sec=S.songs.reduce((a,s)=>a+(s.dur||0),0),b=S.songs.reduce((a,s)=>a+(s.size||0),0);
 $('#libStat').textContent=`${n.toLocaleString()} song${n==1?'':'s'}, ${sec>=86400?(sec/86400).toFixed(1)+' days':sec>=3600?(sec/3600).toFixed(1)+' hrs':Math.round(sec/60)+' min'}`;
 $('#libSize').textContent=b>=1e9?(b/1e9).toFixed(1)+' GB':Math.round(b/1e6)+' MB';
 if(navigator.storage&&navigator.storage.estimate)navigator.storage.estimate().then(e=>{$('#sfill').style.width=Math.max(2,Math.min(100,(e.usage||0)/(e.quota||1)*100*20))+'%'})}
function newPlaylist(){const p={id:uid(),name:'Playlist '+(S.playlists.length+1),songs:[]};S.playlists.push(p);save();go('pl:'+p.id)}
function renderStats(v){const top=[...S.songs].sort((a,b)=>b.plays-a.plays).filter(s=>s.plays).slice(0,10),mx=top[0]?.plays||1,tot=S.songs.reduce((a,s)=>a+(s.plays||0),0),time=S.songs.reduce((a,s)=>a+(s.plays||0)*(s.dur||0),0);
 v.innerHTML=`<h1>Song Stats</h1><div class="stats"><div><b>${S.songs.length}</b>Songs</div><div><b>${tot}</b>Total Plays</div><div><b>${Math.round(time/60)}</b>Minutes Listened</div><div><b>${smart('fav').length}</b>Favourites</div><div><b>${S.playlists.length}</b>Playlists</div></div>
 <h3>Most Played</h3>${top.length?top.map(s=>`<div style="margin:6px 0"><span style="display:inline-block;width:220px">${esc(s.title)}</span><span class="barc" style="width:${s.plays/mx*300}px"></span> ${s.plays}</div>`).join(''):'<p style="color:var(--mut)">Play some songs to see stats.</p>'}`}
function renderRadio(v){v.innerHTML=`<h1>Radio</h1><table>${S.stations.map(s=>`<tr class="song" data-id="${s.id}"><td>📻 ${esc(s.name)}</td><td style="color:var(--mut)">${esc(s.url)}</td><td style="text-align:right"><button class="pl">${cur&&cur.url==s.url&&!stream.paused?'Playing':'Play'}</button> <button class="rm">✕</button></td></tr>`).join('')}</table>
 <div class="row2"><input id="sn" placeholder="Station name"><input id="su" placeholder="Stream URL (http…)"><button id="sa">Add Station</button></div>`;
 v.querySelectorAll('tr').forEach(r=>{const st=S.stations.find(x=>x.id==r.dataset.id);r.querySelector('.pl').onclick=()=>{const s={id:st.id,title:st.name,artist:'Live Radio',stream:true,url:st.url};play(s,[s])};
  r.querySelector('.rm').onclick=()=>{S.stations=S.stations.filter(x=>x!=st);save();render()}});
 $('#sa').onclick=()=>{const u=$('#su').value.trim();if(!/^https?:/.test(u))return toast('Enter a valid URL');S.stations.push({id:uid(),name:$('#sn').value.trim()||u,url:u});save();render()}}
function renderPods(v){v.innerHTML=`<h1>Podcasts</h1><div class="row2"><input id="pu" placeholder="Podcast RSS feed URL"><button id="ps">Subscribe</button></div>
 <p style="color:var(--mut);font-size:11px">Note: some feeds block browser access (CORS). If one fails, try the feed's direct RSS link.</p>
 ${S.podcasts.map(p=>`<details><summary style="cursor:pointer;padding:6px 0"><b>${esc(p.title)}</b> (${p.eps.length}) <button data-u="${p.id}">Unsubscribe</button></summary><table>${p.eps.slice(0,50).map((e,i)=>`<tr class="song"><td>${esc(e.title)}</td><td style="text-align:right"><button data-p="${p.id}" data-i="${i}">Play</button></td></tr>`).join('')}</table></details>`).join('')}`;
 $('#ps').onclick=()=>subscribe($('#pu').value.trim());
 v.querySelectorAll('[data-u]').forEach(b=>b.onclick=e=>{e.preventDefault();S.podcasts=S.podcasts.filter(p=>p.id!=b.dataset.u);save();render()});
 v.querySelectorAll('[data-p]').forEach(b=>b.onclick=()=>{const p=S.podcasts.find(x=>x.id==b.dataset.p),l=p.eps.map((e,i)=>({id:p.id+i,title:e.title,artist:p.title,stream:true,url:e.url}));play(l[+b.dataset.i],l)})}
async function subscribe(u){if(!/^https?:/.test(u))return toast('Enter a feed URL');try{const r=await fetch(u),x=new DOMParser().parseFromString(await r.text(),'text/xml');
 const eps=[...x.querySelectorAll('item')].map(i=>({title:i.querySelector('title')?.textContent||'Episode',url:i.querySelector('enclosure')?.getAttribute('url')})).filter(e=>e.url);
 S.podcasts=S.podcasts.filter(p=>p.feed!=u);S.podcasts.push({id:uid(),feed:u,title:x.querySelector('channel>title')?.textContent||u,eps});save();render();toast(`Subscribed (${eps.length} episodes)`)}
 catch(e){toast('Could not load feed (blocked by CORS or offline)')}}

// ---------- chrome ----------
$('#side').onclick=e=>{const a=e.target.closest('a');if(a)go(a.dataset.v)};
$('#newPl').onclick=newPlaylist;
$('#search').oninput=e=>{search=e.target.value;if(['stats','radio','podcasts','playlists','smarts'].includes(view))view='songs';render()};
$('#theme').innerHTML=Object.keys(THEMES).map(t=>`<option ${t==S.theme?'selected':''}>${t}</option>`).join('');
const applyTheme=()=>{document.documentElement.style.setProperty('--acc',THEMES[S.theme]);document.body.className='dark'};
$('#theme').onchange=e=>{S.theme=e.target.value;save();applyTheme()};
applyTheme();render();updateBar();setArt(null);
window.__music={play,S};

let lastNP='';function npLyrics(){const i=curLyric(),key=(cur&&cur.id)+':'+i+':'+lyrics.length;if(key==lastNP)return;lastNP=key;
 if(!cur){$('#npLyrics').innerHTML='<div class="none">Lyrics appear here while a song plays.</div>';return}
 if(!lyrics.length){$('#npLyrics').innerHTML='<div class="none">No lyrics for this song.<br>Add a matching .lrc file to show them.</div>';return}
 const c=Math.max(0,i),st=Math.max(0,c-2);$('#npLyrics').innerHTML=lyrics.slice(st,st+6).map((l,k)=>`<p class="${st+k==i?'cur':''}">${esc(l.txt)}</p>`).join('')}
$('#moreBtn').onclick=e=>{e.stopPropagation();$('#more').classList.toggle('hidden')};
$('#more').onclick=e=>{if(!e.target.closest('select'))setTimeout(()=>$('#more').classList.add('hidden'),0);const g=e.target.closest('[data-go]');if(g)go(g.dataset.go)};
document.addEventListener('click',e=>{if(!e.target.closest('#more,#moreBtn'))$('#more').classList.add('hidden')});
$('#eqBtn2').onclick=()=>$('#eqBtn').click();$('#queueBtn').onclick=()=>go('queue');
$('#back').onclick=()=>{if(hpos>0)go(hist[--hpos],false)};$('#fwd').onclick=()=>{if(hpos<hist.length-1)go(hist[++hpos],false)};
$('#npMore').onclick=e=>ctxMenu(e,[['Lyrics',()=>lyricsModal(false)],['Karaoke Mode',()=>lyricsModal(true)],[cur&&cur.fav?'Unfavourite':'Favourite',()=>$('#favBtn').click()],['Share…',()=>cur&&share(cur)],['Mini Player',()=>$('#miniBtn').click()],['Up Next',()=>go('queue')]]);
