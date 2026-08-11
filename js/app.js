"use strict";
/* ===================== 数据层 ===================== */
const STORE_KEY = "ipvchat_data";
/* STUN 辅助始终启用：使用国内公共 STUN 获取 srflx 反射地址，绕过 Chrome mDNS 混淆
   （mDNS 把 host 候选改写为 *.local，跨子网/公网无法解析）。srflx 不受 mDNS 影响。
   国内 STUN 仅支持 IPv4；末尾补充 Google STUN（支持 IPv6 AAAA）以在 mDNS 隐藏公网 IPv6 时
   提供 IPv6 srflx 兜底。Google 国内可能不可达，不可达时仅退回 IPv4，不影响连接。
   仅在建连阶段联系 STUN 获取反射地址，消息仍端到端加密、不经过 STUN。局域网亦可启用（无害）。 */
const DEFAULT_STUN_SERVERS = [
  {urls:'stun:stun.miwifi.com:3478'},        // 小米
  {urls:'stun:stun.qq.com:3478'},            // 腾讯
  {urls:'stun:stun.chat.bilibili.com:3478'}, // B站
  {urls:'stun:stun.cloudflare.com:3478'},    // Cloudflare（支持 IPv6 反射；国内可达）
  {urls:'stun:stun.l.google.com:3478'}       // Google（补充候补，支持 IPv6 反射；国内可能不可达，不可达时退回 IPv4）
];

let store = loadStore();
let currentId = null;          // 当前选中联系人 id
let pendingPC = null;          // 握手中的 PeerConnection
let pendingRole = null;        // 'offer' | 'answer'
let pendingChannel = null;
let pendingPeerIps = null;     // 解析对端连接码时暂存其真实 IP（供 finalizeChannel 写入 contact.peerIps）
let connections = new Map();   // contactId -> {chat, file, pc, outSeq, inSeq, pending} (双通道连接)
let channelMap = new Map();    // channel -> {pc, contactId|null, isChat}
let revivable = new Map();     // contactId -> pc（断开后保留的存活通道，用于尝试免交换码恢复）
let peerBye = new Set();       // 收到对端 bye 主动断开的联系人，不自动恢复
let autoReviveTimers = new Map(); // contactId -> timeoutId
let autoReviveRetries = new Map(); // contactId -> 重试次数（autoRevive 失败后指数退避重试，连接成功清零）

/* 心跳：周期 ping/pong 保活 + 探测。iOS 墓碑/安卓息屏恢复后底层 ICE 常短暂 disconnected，
   心跳数据可激活 ICE keepalive 加速恢复，并让 visibilitychange 主动探测连接存活。 */
const HEARTBEAT_INTERVAL = 12000; // 空闲心跳间隔

function defaultStore(){
  return {
    version:4,
    identity:{ id: randId(), name:"用户"+Math.floor(Math.random()*9000+1000) },
    contacts:[],
    messages:{},
    settings:{},
    unread:{}
  };
}
function loadStore(){
  try{
    const raw = localStorage.getItem(STORE_KEY);
    if(!raw) return defaultStore();
    const d = JSON.parse(raw);
    if(!d.identity) d.identity = defaultStore().identity;
    if(!d.contacts) d.contacts = [];
    if(!d.messages) d.messages = {};
    if(!d.settings) d.settings = {};
    if(!d.unread) d.unread = {};
    // 迁移：分离「对端用户名 peerName」与「自定义备注 name」
    d.contacts.forEach(c=>{
      if(c.nameSet===undefined) c.nameSet=false;
      if(c.peerName===undefined) c.peerName = c.nameSet ? '' : (c.name||'');
      // v2.7.6: 补 seq 回执字段（旧数据无 seq 回退时间戳判断）
      if(c.peerDeliveredSeq===undefined) c.peerDeliveredSeq = -1;
      if(c.peerReadSeq===undefined) c.peerReadSeq = -1;
    });
    d.version = 4; // v4 起仅直连，忽略历史 STUN 配置
    return d;
  }catch(e){ console.warn("load fail",e); return defaultStore(); }
}
function saveStore(){ try{ localStorage.setItem(STORE_KEY, JSON.stringify(store)); }catch(e){ console.warn("save fail",e); } }

function randId(){ return "p"+Math.random().toString(36).slice(2,10)+Date.now().toString(36).slice(-4); }
function nowTs(){ return Date.now(); }
function fmtTime(ts){
  const d = new Date(ts), p=n=>String(n).padStart(2,'0');
  const today=new Date(); const same = d.toDateString()===today.toDateString();
  return same? `${p(d.getHours())}:${p(d.getMinutes())}` : `${d.getMonth()+1}/${d.getDate()} ${p(d.getHours())}:${p(d.getMinutes())}`;
}

/* ===================== 联系人 ===================== */
function getContact(id){ return store.contacts.find(c=>c.id===id); }
/* 显示名：有备注则「备注（用户名）」，无备注则显示用户名 */
function contactDisplayText(c){
  const peer = c.peerName || c.name || '未知';
  if(c.nameSet && c.name) return `${c.name}（${peer}）`;
  return peer;
}
function contactDisplayHtml(c){
  const peer = c.peerName || c.name || '未知';
  if(c.nameSet && c.name) return `${escapeHtml(c.name)}<span style="color:var(--mut);font-weight:400">（${escapeHtml(peer)}）</span>`;
  return escapeHtml(peer);
}
function ensureContact(peerId, name){
  let c = getContact(peerId);
  if(!c){ c={id:peerId,name:"",ip:"",lastSeen:0,note:"",nameSet:false,peerName:name||("用户"+Math.floor(Math.random()*9000+1000))}; store.contacts.push(c); }
  if(name) c.peerName = name; // 每次连接同步对端账号用户名
  return c;
}
function isMobile(){ return window.matchMedia && window.matchMedia('(max-width:680px)').matches; }
function selectContact(id, skipLastRead){
  currentId=id;
  if(store.unread[id]){ store.unread[id]=0; saveStore(); }
  updateMobileView(); renderContacts(); renderChat();
  // 仅在已连接时记录 lastReadTs（用户真正在"看新消息"）;
  // 未连接时保留旧值，避免断线后重新点入时刷新为 nowTs，
  // 导致重连后对方离线消息（ts < nowTs）无法触发分界线
  if(!skipLastRead && connections.has(id)){
    const c = getContact(id);
    if(c){ c.lastReadTs = nowTs(); saveStore(); }
  }
  if(id && connections.has(id)) sendReadReceipt(id); // 选中已连接联系人时发已读回执
  if(isMobile() && id){ try{ history.pushState({p2pchat:'chat'},''); }catch(e){} }
}
function goBack(){ currentId=null; updateMobileView(); renderContacts(); renderChat(); }
function backBtn(){
  // 优先 history.back() 让 popstate 统一处理并同步历史栈；
  // 但仅当栈顶确为 chat 条目时——PC 下进入聊天不 pushState，缩窗到手机后历史栈无对应项，
  // 盲目 back 会离开应用或卡死，此时直接 goBack() 退回列表。
  if(currentId && history.state && history.state.p2pchat==='chat'){
    try{ history.back(); }catch(e){ goBack(); }
  } else { goBack(); }
}
function updateMobileView(){
  const app=document.getElementById('app');
  if(currentId) app.classList.add('show-chat'); else app.classList.remove('show-chat');
}

/* ===================== WebRTC ===================== */
function newPC(){
  // STUN 辅助始终启用：填入国内公共 STUN，收集 srflx 候选绕过 mDNS 混淆
  const pc = new RTCPeerConnection({ iceServers: DEFAULT_STUN_SERVERS });
  // 默认处理对端在存活通道上新开的 DataChannel（用于免交换码恢复）
  pc.ondatachannel = e=>{ if(!channelMap.has(e.channel)) bindChannel(e.channel, pc, null, null, e.channel.label==='chat'); };
  return pc;
}

/* 探测本机 IP（IPv4/IPv6）：用 WebRTC ICE host 候选收集（仅直连，无 STUN，避免 srflx 污染本机地址） */
function isRealIp(a){ return !!a && !a.endsWith('.local') && a!=='0.0.0.0' && a!=='::'; }
/* 核心收集：创建临时 PC（启用 STUN）收集 host / srflx 候选，返回 {host4,host6,mdns,srflx}（均为 Set）。
   srflx 为 STUN 反射的公网地址，不受 mDNS 影响——本机真实 IP 被隐藏时用它展示与连接。 */
async function collectMyIps(){
  const ips={host4:new Set(),host6:new Set(),mdns:new Set(),srflx:new Set()};
  let pc;
  try{
    pc=new RTCPeerConnection({iceServers: DEFAULT_STUN_SERVERS});
    pc.createDataChannel('ip');
    pc.onicecandidate=e=>{
      if(!e.candidate||!e.candidate.candidate) return;
      const parts=e.candidate.candidate.split(' ');
      const addr=parts[4], typ=parts[7];
      if(!addr||!typ) return;
      const bucket=(a)=> a.includes(':')?ips.host6:ips.host4;
      if(addr.endsWith('.local')){ ips.mdns.add(addr); }
      else if(typ==='host'){ bucket(addr).add(addr); }
      else if(typ==='srflx'){ ips.srflx.add(addr); } // STUN 反射地址（公网）
    };
    const offer=await pc.createOffer();
    await pc.setLocalDescription(offer);
    await waitIceComplete(pc);
  }catch(e){ /* ignore */ }
  finally{ try{pc&&pc.close();}catch(e){} }
  return ips;
}
async function refreshMyIp(){
  const box=document.getElementById('myIpBox');
  if(box) box.innerHTML='<span class="mi-empty">检测中…</span>';
  const ips=await collectMyIps();
  renderMyIp(ips);
}
function renderMyIp(ips){
  const box=document.getElementById('myIpBox'); if(!box) return;
  const lines=[];
  const push=(tag,set,note)=>{
    set.forEach(a=>{
      const ll = a.toLowerCase().startsWith('fe80')?' (链路本地)':'';
      lines.push(`<div class="mi-line"><span class="mi-tag">${tag}</span>${escapeHtml(a)}${ll}${note?` <span style="color:var(--mut);font-size:10px">${note}</span>`:''}</div>`);
    });
  };
  push('IPv4',ips.host4);
  push('IPv6',ips.host6);
  push('STUN',ips.srflx, '反射公网');
  const hasHost = ips.host4.size + ips.host6.size > 0;
  let html=lines.join('');
  if(!html){
    if(ips.mdns.size){
      html='<div class="mi-note">仅检测到 mDNS（*.local），且 STUN 未返回反射地址。请检查网络能否访问 STUN 服务器。</div>';
    }else{
      html='<div class="mi-empty">未检测到 IP 地址</div>';
    }
  }else if(!hasHost && ips.srflx.size){
    // 本机真实 IP 被 mDNS 全部隐藏，显示的是 STUN 反射的公网地址
    html='<div class="mi-note">⚠ 本机真实 IP 被 mDNS 隐藏，以下为 STUN 反射获取的公网地址（已用于保障连接）：</div>'+html;
  }else if(ips.mdns.size){
    html+='<div class="mi-note">部分本地 IP 被隐藏为 mDNS（*.local）；已启用 STUN 辅助保障连接。</div>';
  }
  box.innerHTML=html;
}

function waitIceComplete(pc){
  return new Promise(res=>{
    if(pc.iceGatheringState==='complete') return res();
    let done=false;
    const finish=()=>{ if(!done){ done=true; pc.removeEventListener('icegatheringstatechange',check); res(); } };
    const check=()=>{ if(pc.iceGatheringState==='complete') finish(); };
    pc.addEventListener('icegatheringstatechange',check);
    // 兜底：gathering 通常很快完成，5s 后用已收集的候选继续，防止异常卡死
    setTimeout(finish, 5000);
  });
}

/* 连接码压缩：用 CompressionStream(deflate-raw) 压缩 JSON，base64 后加 'z' 前缀。
   SDP 高度重复，deflate 可缩短约 60%。旧浏览器无 CompressionStream 时回退原 base64 + 'b' 前缀。
   decodeSignal 兼容三种：'z'=压缩、'b'=新未压缩、无前缀=旧版连接码。 */
function bytesToB64(bytes){
  let bin='';
  for(let i=0;i<bytes.length;i++) bin += String.fromCharCode(bytes[i]);
  return btoa(bin);
}
function b64ToBytes(b64){
  const bin=atob(b64); const bytes=new Uint8Array(bin.length);
  for(let i=0;i<bin.length;i++) bytes[i]=bin.charCodeAt(i);
  return bytes;
}
function utf8ToB64(str){
  const bytes = new TextEncoder().encode(str);
  let bin='';
  for(let i=0;i<bytes.length;i++) bin += String.fromCharCode(bytes[i]);
  return btoa(bin);
}
function b64ToUtf8(b64){
  const bin=atob(b64); const bytes=new Uint8Array(bin.length);
  for(let i=0;i<bin.length;i++) bytes[i]=bin.charCodeAt(i);
  return new TextDecoder().decode(bytes);
}
async function encodeSignal(obj){
  const json = JSON.stringify(obj);
  if(typeof CompressionStream !== 'undefined'){
    try{
      const input = new TextEncoder().encode(json);
      const stream = new Blob([input]).stream().pipeThrough(new CompressionStream('deflate-raw'));
      const buf = new Uint8Array(await new Response(stream).arrayBuffer());
      return 'z' + bytesToB64(buf);
    }catch(e){}
  }
  return 'b' + utf8ToB64(json);
}
async function decodeSignal(s){
  s = s.trim();
  const head = s[0];
  let json;
  if(head === 'z'){
    const bytes = b64ToBytes(s.slice(1));
    const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream('deflate-raw'));
    const buf = await new Response(stream).arrayBuffer();
    json = new TextDecoder().decode(buf);
  }else if(head === 'b'){
    json = b64ToUtf8(s.slice(1));
  }else{
    json = b64ToUtf8(s); // 兼容旧版无前缀连接码
  }
  return JSON.parse(json);
}

/* ===== 二维码生成与扫描（v2.9.0）=====
   生成：qrcode-generator 渲染到 canvas，可放大/保存/系统分享。
   扫描：jsQR 解析摄像头帧或上传图片。连接码经 v2.8.0 deflate 压缩后约 800 字符，
   纠错级 L 下 QR 版本 ~20（97×97 模块）可容纳且更易扫；旧浏览器回退未压缩码过长时生成会失败并提示用文本复制。 */
/* 生成二维码并弹窗展示 */
function showQrCode(text, title){
  if(typeof qrcode === 'undefined') return toast("二维码库未加载");
  if(!text) return toast("暂无内容可生成二维码");
  let qr;
  try{
    qr = qrcode(0, 'L'); // typeNumber=0 自动选最小版本，纠错级 L（7%）：屏幕二维码无污损，L 级模块数最少、每块最大，最易扫描
    qr.addData(text);
    qr.make();
  }catch(e){ return toast("连接码过长，无法生成二维码，请用文本复制"); }
  const canvas = qrToCanvas(qr, 8);
  document.getElementById('qrTitle').textContent = title || '二维码';
  const box = document.getElementById('qrCanvasBox');
  box.innerHTML='';
  canvas.className='qr-canvas';
  canvas.title='点击放大';
  box.appendChild(canvas);
  document.getElementById('qrLarge').onclick=()=>openQrLarge(canvas);
  document.getElementById('qrSave').onclick=()=>saveQr(canvas);
  document.getElementById('qrShare').onclick=()=>shareQr(canvas, title);
  document.getElementById('dlgQr').classList.add('show');
}
/* qrcode-generator 对象 → canvas（cell=每模块像素，margin=静默区模块数） */
function qrToCanvas(qr, cell){
  const n = qr.getModuleCount();
  const margin = 4;
  const size = (n + margin*2) * cell;
  const canvas = document.createElement('canvas');
  canvas.width = canvas.height = size;
  const ctx = canvas.getContext('2d');
  ctx.fillStyle='#fff'; ctx.fillRect(0,0,size,size);
  ctx.fillStyle='#000';
  for(let r=0;r<n;r++) for(let c=0;c<n;c++){
    if(qr.isDark(r,c)) ctx.fillRect((c+margin)*cell,(r+margin)*cell,cell,cell);
  }
  return canvas;
}
/* 放大查看：最近邻缩放保持模块清晰边界 */
function openQrLarge(srcCanvas){
  const box = document.getElementById('qrLargeBox');
  box.innerHTML='';
  const big = document.createElement('canvas');
  const scale = Math.max(2, Math.floor(720 / srcCanvas.width));
  big.width = srcCanvas.width * scale;
  big.height = srcCanvas.height * scale;
  const ctx = big.getContext('2d');
  ctx.imageSmoothingEnabled = false;
  ctx.drawImage(srcCanvas, 0, 0, big.width, big.height);
  big.className='qr-large';
  box.appendChild(big);
  document.getElementById('qrLargeSave').onclick=()=>saveQr(big);
  document.getElementById('qrLargeShare').onclick=()=>shareQr(big, 'P2PChat 连接码');
  document.getElementById('dlgQrLarge').classList.add('show');
}
/* 保存二维码为本地 PNG */
function saveQr(canvas){
  canvas.toBlob(blob=>{
    if(!blob) return toast("保存失败");
    const a=document.createElement('a');
    a.href=URL.createObjectURL(blob);
    a.download='p2pchat-qrcode.png';
    document.body.appendChild(a); a.click(); document.body.removeChild(a);
    setTimeout(()=>URL.revokeObjectURL(a.href),2000);
    toast("已保存二维码图片");
  },'image/png');
}
/* 调用系统 Web Share API 分享到社交 app，不支持时回退保存 */
function shareQr(canvas, title){
  if(!navigator.share){ saveQr(canvas); return toast("当前环境不支持系统分享，已保存图片"); }
  canvas.toBlob(async blob=>{
    if(!blob) return toast("分享失败");
    const file = new File([blob], 'p2pchat-qrcode.png', {type:'image/png'});
    try{
      if(navigator.canShare && !navigator.canShare({files:[file]})){
        saveQr(canvas); return toast("当前环境不支持分享图片，已保存");
      }
      await navigator.share({files:[file], title: title||'P2PChat 连接码', text:'扫描此二维码建立 P2PChat 加密连接'});
    }catch(e){ if(e && e.name!=='AbortError') toast("分享失败: "+e.message); }
  },'image/png');
}
/* 扫描二维码：摄像头实时识别 + 上传图片识别，成功回调 callback(text) */
let scanStream=null, scanRAF=null;
function showQrScanner(callback){
  if(typeof jsQR === 'undefined') return toast("二维码库未加载");
  const ov=document.getElementById('dlgScan');
  const video=document.getElementById('scanVideo');
  const status=document.getElementById('scanStatus');
  ov.classList.add('show');
  status.textContent='正在启动摄像头…';
  if(video) video.srcObject=null;
  if(!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia){
    status.textContent='当前环境不支持摄像头，请改用「📁 上传二维码」按钮';
    return;
  }
  navigator.mediaDevices.getUserMedia({video:{facingMode:'environment', width:{ideal:1280}, height:{ideal:720}}}).then(stream=>{
    scanStream=stream; video.srcObject=stream;
    video.play().catch(()=>{});
    status.textContent='将二维码对准摄像头…';
    scanLoop(video, (text)=>{ closeScanner(); callback(text); });
  }).catch(e=>{
    status.textContent='摄像头不可用：'+(e.message||e.name)+'。请改用「📁 上传二维码」按钮';
  });
}
function scanLoop(video, onFound){
  const canvas=document.createElement('canvas');
  const ctx=canvas.getContext('2d',{willReadFrequently:true});
  const MAX=640; // 降采样上限：jsQR 解析速度与帧率平衡，帧率高→尝试次数多→命中率高
  const tick=()=>{
    if(!scanStream) return; // 已关闭则停止
    if(video.readyState>=video.HAVE_ENOUGH_DATA && video.videoWidth){
      const vw=video.videoWidth, vh=video.videoHeight;
      const scale=Math.min(1, MAX/Math.max(vw,vh));
      const w=Math.round(vw*scale), h=Math.round(vh*scale);
      canvas.width=w; canvas.height=h;
      ctx.drawImage(video,0,0,w,h);
      const img=ctx.getImageData(0,0,w,h);
      const code=jsQR(img.data, w, h, {inversionAttempts:'attemptBoth'});
      if(code && code.data){ onFound(code.data); return; }
    }
    scanRAF=requestAnimationFrame(tick);
  };
  tick();
}
/* 从图片解析二维码（多尺度尝试提升识别率：640 快扫 → 1280 细节 → 2000 高清，任一命中即返回） */
function decodeQrImage(img){
  const natW=img.naturalWidth||img.width, natH=img.naturalHeight||img.height;
  const maxes=[640, 1280, 2000];
  for(const max of maxes){
    let w=natW, h=natH;
    if(max>0 && (w>max||h>max)){ const s=max/Math.max(w,h); w=Math.round(w*s); h=Math.round(h*s); }
    if(w<1||h<1) continue;
    const c=document.createElement('canvas'); c.width=w; c.height=h;
    const x=c.getContext('2d',{willReadFrequently:true});
    x.drawImage(img,0,0,w,h);
    const imgData=x.getImageData(0,0,w,h);
    const code=jsQR(imgData.data, w, h, {inversionAttempts:'attemptBoth'});
    if(code && code.data) return code.data;
  }
  return null;
}
/* 关闭扫描：停止摄像头流与帧循环 */
function closeScanner(){
  if(scanRAF) cancelAnimationFrame(scanRAF); scanRAF=null;
  if(scanStream){ scanStream.getTracks().forEach(t=>t.stop()); scanStream=null; }
  const v=document.getElementById('scanVideo'); if(v) v.srcObject=null;
  document.getElementById('dlgScan').classList.remove('show');
}
/* 扫码结果填入指定输入框 */
function scanTo(textareaId){
  showQrScanner(text=>{
    const el=document.getElementById(textareaId);
    if(el){ el.value=text; toast("已识别并填入"); }
  });
}
/* 上传二维码图片识别并填入（独立入口，不开摄像头） */
function uploadQrTo(textareaId){
  if(typeof jsQR === 'undefined') return toast("二维码库未加载");
  const input=document.getElementById('scanFileInput');
  input.onchange=(e)=>{
    const f=e.target.files && e.target.files[0]; e.target.value=''; // 允许重复选择同一文件
    if(!f) return;
    toast("正在识别二维码，请稍候…", 6000);
    const url=URL.createObjectURL(f);
    const img=new Image();
    img.onload=()=>{
      const r=decodeQrImage(img);
      URL.revokeObjectURL(url);
      if(r){ const el=document.getElementById(textareaId); if(el){ el.value=r; toast("已识别并填入"); } }
      else toast("未识别到二维码，请换一张图片");
    };
    img.onerror=()=>{ URL.revokeObjectURL(url); toast("图片读取失败"); };
    img.src=url;
  };
  input.click();
}

/* 检查 localDescription 中是否含有「真实 IP 的 host 候选」（非 mDNS） */
function hasRealHostCandidate(pc){
  const sdp = (pc.localDescription && pc.localDescription.sdp) || '';
  return sdp.split('\n').some(l=>{
    if(!l.startsWith('a=candidate=') || !l.includes(' typ host')) return false;
    const addr = l.split(' ')[4];
    return addr && !addr.endsWith('.local');
  });
}
/* 从已收集完成的 localDescription 中提取本机真实 IP（host + srflx，排除 .local）。
   复用握手 PC 已收集的候选，避免再开临时 PC 做 STUN 收集（省一次往返）。 */
function extractIpsFromPc(pc){
  const sdp = (pc.localDescription && pc.localDescription.sdp) || '';
  const ips = new Set();
  sdp.split('\n').forEach(l=>{
    if(!l.startsWith('a=candidate=')) return;
    const parts = l.split(' ');
    const addr = parts[4], typ = parts[7];
    if(!addr || !typ) return;
    if((typ==='host' || typ==='srflx') && isRealIp(addr)) ips.add(addr);
  });
  return [...ips];
}

/* 连接诊断：STUN 始终启用，根据本机是否有真实 host 候选 / 对端 IP 给出场景化提示 */
function connectDiagnose(pc){
  const hasReal = hasRealHostCandidate(pc);
  const c = currentId && getContact(currentId);
  const peerIps = (c && c.peerIps) || pendingPeerIps || [];
  const peerStr = peerIps.length ? `对端地址：${peerIps.join(' / ')}。` : '';
  if(!hasReal){
    return `⚠ 连接未建立。本机真实 IP 被 mDNS 隐藏（*.local），已通过 STUN 获取反射地址。若仍失败请确认：①系统防火墙放行入站 UDP ②网络可访问 STUN 服务器 ③双方在同一局域网或均具公网 IP。${peerStr}`;
  }
  return `⚠ 连接未建立。本机已暴露真实 IP，请确认对端：①防火墙放行入站 UDP ②未因 mDNS 隐藏真实 IP ③与你在同一局域网或具公网 IP。${peerStr}`;
}

/* 清理指定联系人的所有传输 objectURL（文件/图片/视频/语音），释放 Blob 内存 */
function revokeContactUrls(contactId){
  const arr = store.messages[contactId] || [];
  for(const m of arr){
    if(m.file && m.file.fid){ const u=fileUrls.get(m.file.fid); if(u){ URL.revokeObjectURL(u); fileUrls.delete(m.file.fid); } }
    if(m.image && m.image.iid){ const u=imageUrls.get(m.image.iid); if(u){ URL.revokeObjectURL(u); imageUrls.delete(m.image.iid); } }
    if(m.video && m.video.vid){ const u=videoUrls.get(m.video.vid); if(u){ URL.revokeObjectURL(u); videoUrls.delete(m.video.vid); } }
    if(m.audio && m.audio.aid){ const u=audioUrls.get(m.audio.aid); if(u){ URL.revokeObjectURL(u); audioUrls.delete(m.audio.aid); } }
  }
}
/* 清理所有传输 objectURL（退出时调用） */
function revokeAllUrls(){
  for(const u of fileUrls.values()) URL.revokeObjectURL(u);
  for(const u of imageUrls.values()) URL.revokeObjectURL(u);
  for(const u of videoUrls.values()) URL.revokeObjectURL(u);
  for(const u of audioUrls.values()) URL.revokeObjectURL(u);
  fileUrls.clear(); imageUrls.clear(); videoUrls.clear(); audioUrls.clear();
}
/* 清理指定联系人的 Audio 播放器，释放内存 */
function stopContactAudioPlayers(contactId){
  const arr = store.messages[contactId] || [];
  for(const m of arr){
    if(m.audio && m.audio.aid){
      const au = audioPlayers.get(m.audio.aid);
      if(au){ try{ au.pause(); au.src=''; au.load(); }catch(e){} }
      audioPlayers.delete(m.audio.aid);
    }
  }
}
/* 清理所有 Audio 播放器（退出时调用） */
function stopAllAudioPlayers(){
  for(const au of audioPlayers.values()){
    try{ au.pause(); au.src=''; au.load(); }catch(e){}
  }
  audioPlayers.clear();
}

/* 连接建立看门狗：真正开始 ICE 连通后（邀请方提交应答码 / 被邀方生成应答码）若 90s 内未建立连接，给出诊断提示。
   注意：邀请方生成邀请码阶段不启动看门狗——此时仍在等对方人工回发应答码，交换时间不可控，不应计入连通超时。
   90s 容错覆盖双方交换连接码/二维码（扫码、复制粘贴）+ 跨网络 IPv6 ICE 连通；ICE failed 事件会立即报错，看门狗仅在卡住时兜底。 */
let connectWatchdog=null;
function startConnectWatchdog(pc, label){
  clearConnectWatchdog();
  connectWatchdog = setTimeout(()=>{
    const established = [...channelMap.values()].some(i=>i.pc===pc && i.contactId);
    if(!established){
      toast(connectDiagnose(pc), 10000);
      // 超时清理：释放 pendingPC 及握手资源
      if(pendingPC===pc){ cleanupPending(); }
      else{ try{ pc.close(); }catch(e){} }
    }
  }, 90000);
}
function clearConnectWatchdog(){ if(connectWatchdog){ clearTimeout(connectWatchdog); connectWatchdog=null; } }

/* 快速重连：先尝试基于存活通道免交换码恢复，失败再回退到交换连接码 */
async function quickReconnect(){
  if(!currentId) return;
  const c=getContact(currentId); if(!c) return;
  if(connections.has(currentId)){ toast("已处于连接状态"); return; }
  // 1) 先尝试恢复
  if(revivable.has(currentId)){
    showConnectDialog([{step:`正在尝试恢复与「${escapeHtml(contactDisplayText(c))}」的连接…`, body:`
      <p style="font-size:12px;color:var(--mut)">尝试复用上一次尚存的直连通道，无需交换码（仅双方页面都未关闭时可能成功）…</p>
      <div class="mi-note" id="reviveStatus">尝试中…</div>`}]);
    const ok = await attemptRevive(currentId);
    if(ok){ toast("已恢复连接"); return; } // finalizeChannel 会关弹窗并切换视图
    const rs=document.getElementById('reviveStatus');
    if(rs) rs.textContent="恢复失败，转为重新交换连接码。";
  }
  // 2) 回退到手动交换
  showConnectDialog([
    {step:`重新交换连接码 · 与「${escapeHtml(contactDisplayText(c))}」重连`, body:`
      <p style="font-size:12px;color:var(--mut)">恢复失败（页面已刷新或对端已关闭）。因 WebRTC 会话信息每次临时生成，需双方重新交换一次连接码。联系人信息与历史记录会自动延续。</p>
      <div class="row">
        <button onclick="startInvite()">我发起（生成邀请码）</button>
        <button class="ghost" onclick="startAccept()">我接受（粘贴邀请码）</button>
      </div>`}
  ]);
}
/* 在存活的 PC 上重新打开 DataChannel，成功则免交换码恢复 */
function attemptRevive(contactId){
  return new Promise(res=>{
    if(connections.has(contactId)){ res(true); return; } // 已连接
    const pc = revivable.get(contactId);
    if(!pc){ res(false); return; }
    const st = pc.iceConnectionState;
    if(st==='closed' || st==='failed'){
      // ICE 已彻底失效：清理 PC，放弃恢复
      try{ pc.close(); }catch(e){}
      revivable.delete(contactId);
      res(false); return;
    }
    if(st!=='connected' && st!=='completed'){
      // disconnected 等：iOS 墓碑/息屏恢复后 ICE 常短暂 disconnected，底层网络未变时可自行恢复。
      // 不破坏 PC，保留 revivable 供后续重试（attemptRevive 重开 DataChannel 需 ICE 已连通）。
      res(false); return;
    }
    let chatCh, fileCh;
    try{
      chatCh = pc.createDataChannel('chat',{ordered:true});
      fileCh = pc.createDataChannel('file',{ordered:true});
    }
    catch(e){ res(false); return; }
    let opened=0;
    const to=setTimeout(()=>{ try{chatCh.close();fileCh.close();}catch(e){} res(false); }, 5000);
    const onOpen=(ch,isC)=>{ opened++; bindChannel(ch, pc, null, null, isC); if(opened>=2){ clearTimeout(to); res(true); } };
    chatCh.onopen=()=>onOpen(chatCh, true);
    fileCh.onopen=()=>onOpen(fileCh, false);
    chatCh.onerror=()=>{ clearTimeout(to); res(false); };
    fileCh.onerror=()=>{ clearTimeout(to); res(false); };
  });
}

/* 邀请方：生成邀请码 */
async function startInvite(){
  pendingRole='offer';
  showConnectDialog([{step:"第 1 步 · 正在生成邀请码", body:`
    <div class="gen-loading"><span class="spinner"></span>正在创建加密连接、收集 STUN 反射地址…</div>`}]);
  cleanupPending();
  const pc = newPC(); pendingPC = pc;
  const chatCh = pc.createDataChannel("chat",{ordered:true});
  const fileCh = pc.createDataChannel("file",{ordered:true});
  pendingChannel = chatCh;
  bindChannel(chatCh, pc, null, null, true);
  bindChannel(fileCh, pc, null, null, false);
  const offer = await pc.createOffer();
  await pc.setLocalDescription(offer);
  await waitIceComplete(pc);
  if(pendingPC !== pc) return; // 用户在等待期间点了取消，中止生成
  // 不在此处启动连接看门狗：邀请方还在等对方人工回发应答码，交换时间不可控，不应计入连通超时。
  // 看门狗改在 finalizeOffer() 提交应答码、真正开始 ICE 连通后启动。
  const mdnsWarn = hasRealHostCandidate(pc) ? '' :
    '<div class="mi-note">ℹ 本机真实 IP 被 mDNS 隐藏（*.local），已通过 STUN 辅助获取反射地址以保障连接。</div>';
  const code = await encodeSignal({type:"offer", sdp: pc.localDescription, identity: store.identity, ips: extractIpsFromPc(pc)});
  showConnectDialog([
    {step:"第 1 步（共 3 步） · 你是邀请方", body:`
      <p style="font-size:12px;color:var(--mut)">把下面的<b>邀请码</b>发给对方（任意聊天工具），让对方点「接受连接」并粘贴。</p>
      <textarea class="codebox" id="codeOut" readonly>${code}</textarea>
      ${mdnsWarn}
      <div class="row"><button onclick="copyText(document.getElementById('codeOut').value)">复制邀请码</button><button class="ghost" onclick="showQrCode(document.getElementById('codeOut').value,'邀请码二维码')">📱 二维码</button></div>`},
    {step:"第 3 步 · 等对方回发应答码后粘贴", body:`
      <textarea class="codebox" id="codeIn" placeholder="在此粘贴对方回发的应答码..."></textarea>
      <div class="row"><button onclick="finalizeOffer()">完成连接</button><button class="ghost" onclick="scanTo('codeIn')">📷 相机扫码</button><button class="ghost" onclick="uploadQrTo('codeIn')">📁 上传二维码</button></div>`}
  ]);
}
async function finalizeOffer(){
  const s = document.getElementById('codeIn').value.trim();
  if(!s) return toast("请粘贴应答码");
  const pc = pendingPC;
  if(!pc) return toast("连接已取消，请重新开始");
  try{
    const obj = await decodeSignal(s);
    if(obj.type!=='answer') return toast("这不是应答码");
    pendingPeerIps = Array.isArray(obj.ips) ? obj.ips : null; // 暂存对端真实 IP
    await pc.setRemoteDescription(new RTCSessionDescription(obj.sdp));
    if(pendingPC !== pc) return; // 用户在等待期间点了取消，中止
    toast("已提交，正在建立连接…", 3000);
    document.getElementById('dlgConnect').classList.remove('show');
    startConnectWatchdog(pc, "连接");
  }catch(e){ toast("应答码无效: "+e.message); }
}

/* 被邀方：粘贴邀请码，生成应答码 */
async function startAccept(){
  pendingRole='answer';
  cleanupPending();
  showConnectDialog([
    {step:"第 2 步 · 你是被邀方", body:`
      <p style="font-size:12px;color:var(--mut)">粘贴对方发来的<b>邀请码</b>：</p>
      <textarea class="codebox" id="codeIn" placeholder="在此粘贴邀请码..."></textarea>
      <div class="row"><button onclick="acceptOffer()">生成应答码</button><button class="ghost" onclick="scanTo('codeIn')">📷 相机扫码</button><button class="ghost" onclick="uploadQrTo('codeIn')">📁 上传二维码</button></div>`},
    {step:"生成后 · 把应答码回发给对方", body:`
      <textarea class="codebox" id="codeOut" readonly placeholder="应答码将显示在这里..."></textarea>
      <div class="row"><button onclick="copyText(document.getElementById('codeOut').value)">复制应答码</button><button class="ghost" onclick="showQrCode(document.getElementById('codeOut').value,'应答码二维码')">📱 二维码</button></div>`}
  ]);
}
async function acceptOffer(){
  const s = document.getElementById('codeIn').value.trim();
  if(!s) return toast("请粘贴邀请码");
  try{
    const obj = await decodeSignal(s);
    if(obj.type!=='offer') return toast("这不是邀请码");
    pendingPeerIps = Array.isArray(obj.ips) ? obj.ips : null; // 暂存对端真实 IP
    // 立即显示生成中提示，避免用户以为点击无反应（STUN 收集候选需要网络往返）
    const co=document.getElementById('codeOut');
    if(co){ co.value='⏳ 正在生成应答码，收集 STUN 反射地址…'; }
    toast("正在生成应答码…", 3000);
    const pc = newPC(); pendingPC = pc;
    pc.ondatachannel = e=>{
      if(e.channel.label==='chat'){
        pendingChannel = e.channel;
        bindChannel(e.channel, pc, obj.identity.id, obj.identity.name, true);
      } else if(e.channel.label==='file'){
        bindChannel(e.channel, pc, null, null, false);
      }
    };
    await pc.setRemoteDescription(new RTCSessionDescription(obj.sdp));
    const ans = await pc.createAnswer();
    await pc.setLocalDescription(ans);
    await waitIceComplete(pc);
    if(pendingPC !== pc) return; // 用户在等待期间点了取消，中止生成
    startConnectWatchdog(pc, "连接");
    if(!hasRealHostCandidate(pc)) toast("ℹ 本机真实 IP 被 mDNS 隐藏，已通过 STUN 辅助获取反射地址", 5000);
    const code = await encodeSignal({type:"answer", sdp: pc.localDescription, identity: store.identity, ips: extractIpsFromPc(pc)});
    document.getElementById('codeOut').value = code;
    toast("已生成应答码，请复制回发给对方");
  }catch(e){ toast("邀请码无效: "+e.message); }
}

function bindChannel(channel, pc, knownPeerId, knownPeerName, isChat){
  channel.binaryType='arraybuffer'; // 接收文件分块用 ArrayBuffer
  channelMap.set(channel, {pc, contactId: knownPeerId||null, isChat: !!isChat});
  channel.onopen = ()=> onChannelOpen(channel, knownPeerId, knownPeerName, !!isChat);
  channel.onmessage = e=> onChannelMsg(channel, e.data);
  channel.onclose = ()=> onChannelClose(channel);
  channel.onerror = ()=> onChannelClose(channel);
  // ICE 状态监听仅 chat 通道绑定（避免 file 通道重复触发）
  if(isChat){
    pc.oniceconnectionstatechange = ()=>{
      const st = pc.iceConnectionState;
      if(st==='failed'){ clearConnectWatchdog(); toast("ICE 连接失败：请确认双方在同一局域网或均有公网 IP，并放行入站 UDP；STUN 已启用，若仍失败请检查网络能否访问 STUN 服务器", 7000); onChannelClose(channel); }
      else if(st==='disconnected'){
        // 不立即清理：iOS 墓碑/安卓息屏恢复后常短暂进入 disconnected，底层网络未变时 ICE 可自行恢复。
        // 主动发 ping 激活 ICE keepalive，加速恢复；若持续无法恢复最终会 failed → onChannelClose。
        toast("连接中断，尝试恢复中...");
        const info = channelMap.get(channel);
        if(info && info.contactId) sendPing(info.contactId);
      }
    };
  }
}

function onChannelOpen(channel, peerId, peerName, isChat){
  if(!isChat){
    // file 通道打开：如果 chat 已登记，将 file 通道补连到 connections
    const info = channelMap.get(channel);
    if(!info) return;
    for(const [ch, inf] of channelMap){
      if(inf.pc===info.pc && inf.isChat && inf.contactId){
        const conn = connections.get(inf.contactId);
        if(conn && !conn.file){
          conn.file = channel;
          info.contactId = inf.contactId;
        }
        break;
      }
    }
    return;
  }
  // 发送本机身份
  try{ channel.send(JSON.stringify({type:"hello", identity: store.identity})); }catch(e){}
  if(peerId){
    // 被邀方：邀请码里已带邀请方身份，直接登记
    finalizeChannels(channel, peerId, peerName);
  }else{
    // 邀请方：需等对端 hello 才知道身份
    toast("连接已建立，等待对端身份...");
  }
}
function onChannelMsg(channel, data){
  // 二进制：文件/图片分块（仅 file 通道收发）
  // meta/end 走 chat 通道避免队头阻塞，incoming 状态挂在 chat 条目上；
  // 二进制分块到达 file 通道时需回溯同 PC 的 chat 条目查找 incoming 状态
  if(typeof data !== 'string'){
    let target = channelMap.get(channel);
    if(target && !target.incomingFile && !target.incomingImage && !target.incomingVideo && !target.incomingAudio){
      for(const [ch, inf] of channelMap){
        if(inf.pc===target.pc && inf.isChat && inf.contactId===target.contactId){
          target = inf; break;
        }
      }
    }
    if(target && target.incomingFile){
      target.incomingFile.chunks.push(data);
      target.incomingFile.received += data.byteLength;
      const stf=fileTransfers.get(target.incomingFile.fid); if(stf) stf.received=target.incomingFile.received;
      updateFileProgress(target.incomingFile.fid);
    }else if(target && target.incomingImage){
      target.incomingImage.chunks.push(data);
      target.incomingImage.received += data.byteLength;
      const sti=imageTransfers.get(target.incomingImage.iid); if(sti) sti.received=target.incomingImage.received;
      updateImageProgress(target.incomingImage.iid);
    }else if(target && target.incomingVideo){
      target.incomingVideo.chunks.push(data);
      target.incomingVideo.received += data.byteLength;
      const stv=videoTransfers.get(target.incomingVideo.vid); if(stv) stv.received=target.incomingVideo.received;
      updateVideoProgress(target.incomingVideo.vid);
    }else if(target && target.incomingAudio){
      target.incomingAudio.chunks.push(data);
      target.incomingAudio.received += data.byteLength;
      const sta=audioTransfers.get(target.incomingAudio.aid); if(sta) sta.received=target.incomingAudio.received;
      updateAudioProgress(target.incomingAudio.aid);
    }
    return;
  }
  let m; try{ m=JSON.parse(data); }catch{ return; }
  if(m.type==='hello'){
    const info=channelMap.get(channel);
    // 已连接的同联系人发来 hello（改名同步）：仅更新用户名，不重走连接流程
    if(info && info.contactId && info.contactId===m.identity.id && connections.has(info.contactId)){
      const c=getContact(info.contactId);
      if(c){ c.peerName=m.identity.name||c.peerName; c.lastSeen=nowTs(); saveStore(); renderContacts(); if(info.contactId===currentId) renderTopbar(); }
      return;
    }
    finalizeChannels(channel, m.identity.id, m.identity.name);
    return;
  }
  const info = channelMap.get(channel);
  const cId = info && info.contactId;
  if(!cId) return; // 身份未确认前丢弃业务消息
  if(m.type==='msg'){
    const conn = connections.get(cId);
    // seq 去重：已处理过的消息只回累积 ACK，不重复 addMessage（弱网重传时）
    if(conn && typeof m.seq==='number'){
      if(m.seq < conn.inSeq){ sendAck(cId, conn.inSeq-1); return; }
      conn.inSeq = Math.max(conn.inSeq, m.seq+1);
      sendAck(cId, conn.inSeq-1);
    }
    addMessage(cId, 'in', m.text, m.ts, m.seq);
    if(cId===currentId) sendReadReceipt(cId);
  }
  else if(m.type==='file-meta'){ startReceiveFile(cId, info, m); if(cId===currentId) sendReadReceipt(cId); }
  else if(m.type==='file-end'){ finishReceiveFile(cId, info, m.fid); }
  else if(m.type==='image-meta'){ startReceiveImage(cId, info, m); if(cId===currentId) sendReadReceipt(cId); }
  else if(m.type==='image-end'){ finishReceiveImage(cId, info, m.iid); }
  else if(m.type==='video-meta'){ startReceiveVideo(cId, info, m); if(cId===currentId) sendReadReceipt(cId); }
  else if(m.type==='video-end'){ finishReceiveVideo(cId, info, m.vid); }
  else if(m.type==='audio-meta'){ startReceiveAudio(cId, info, m); if(cId===currentId) sendReadReceipt(cId); }
  else if(m.type==='audio-end'){ finishReceiveAudio(cId, info, m.aid); }
  else if(m.type==='read'){
    const c = getContact(cId);
    if(c){
      if(typeof m.seq==='number') c.peerReadSeq = Math.max(c.peerReadSeq||0, m.seq);
      c.peerReadTs = m.ts; // 保留时间戳用于文件/图片消息回退
      saveStore(); if(cId===currentId) requestAnimationFrame(()=>refreshMessageReadStatus(cId));
    }
  }
  else if(m.type==='ack'){
    const conn = connections.get(cId);
    if(conn){
      for(const [seq, p] of conn.pending){
        if(seq <= m.seq){ clearTimeout(p.timer); conn.pending.delete(seq); }
      }
    }
    const c = getContact(cId);
    if(c){
      c.peerDeliveredSeq = Math.max(c.peerDeliveredSeq||0, m.seq);
      c.peerDeliveredTs = nowTs(); // 保留时间戳用于文件/图片消息回退
      saveStore(); if(cId===currentId) requestAnimationFrame(()=>refreshMessageReadStatus(cId));
    }
  }
  else if(m.type==='delivered'){
    const c = getContact(cId);
    if(c && (!c.peerDeliveredTs || m.ts > c.peerDeliveredTs)){
      c.peerDeliveredTs = m.ts; saveStore(); if(cId===currentId) requestAnimationFrame(()=>refreshMessageReadStatus(cId));
    }
  }
  else if(m.type==='bye'){ appendSys(cId,"对方已断开"); peerBye.add(cId); }
  else if(m.type==='ping'){ // 心跳探测：立即回 pong，激活双方 ICE keepalive
    const conn = connections.get(cId);
    if(conn && conn.chat){ try{ conn.chat.send(JSON.stringify({type:'pong', ts:m.ts})); }catch(e){} }
  }
  else if(m.type==='pong'){ /* 心跳回应：连接存活，无需处理 */ }
  // 收到消息发已送达回执（msg 已通过 ACK 覆盖，此处仅对无 seq 消息和 file-meta 等发 delivered）
  if(m.type!=='delivered' && m.type!=='read' && m.type!=='ack' && m.type!=='ping' && m.type!=='pong'){
    // 仅非 msg 或旧版无 seq 的 msg 发 delivered（新版 msg 走 ACK）
    if(m.type!=='msg' || typeof m.seq!=='number') sendDeliveredReceipt(cId);
  }
}
/* 心跳保活：周期性 ping 防止 NAT 映射超时、激活 ICE keepalive；ping/pong 不参与可靠性与
   回执，仅作活性探测。iOS 墓碑/安卓息屏恢复后立即补发 ping 可加速 ICE 从 disconnected 恢复。 */
function sendPing(cId){
  const conn = connections.get(cId);
  if(conn && conn.chat && conn.chat.readyState==='open'){
    try{ conn.chat.send(JSON.stringify({type:'ping', ts:nowTs()})); }catch(e){}
  }
}
function startHeartbeat(cId){
  const conn = connections.get(cId);
  if(!conn) return;
  stopHeartbeat(conn);
  conn.hbTimer = setInterval(()=>sendPing(cId), HEARTBEAT_INTERVAL);
}
function stopHeartbeat(conn){
  if(conn && conn.hbTimer){ clearInterval(conn.hbTimer); conn.hbTimer=null; }
}
function finalizeChannels(chatCh, peerId, peerName){
  const chatInfo = channelMap.get(chatCh);
  if(!chatInfo) return;
  const pc = chatInfo.pc;
  // 查找同一 PC 上的 file 通道（可能尚未到达，由 onChannelOpen 补连）
  let fileCh = null;
  for(const [ch, info] of channelMap){
    if(info.pc===pc && !info.isChat){ fileCh = ch; break; }
  }
  const oldId = chatInfo.contactId;
  if(oldId && oldId!==peerId){
    const oc = connections.get(oldId);
    if(oc){ for(const [seq,p] of oc.pending) clearTimeout(p.timer); oc.pending.clear(); }
    connections.delete(oldId);
  }
  // 在 channelMap 中对两个通道写入 contactId
  chatInfo.contactId = peerId;
  if(fileCh){ const fi = channelMap.get(fileCh); if(fi) fi.contactId = peerId; }
  const c = ensureContact(peerId, peerName);
  // 从历史消息恢复 seq 基线，避免重连后 outSeq/inSeq 归零与持久化的 peerReadSeq/peerDeliveredSeq 错位
  // （否则新发出 seq 0 <= 旧 peerReadSeq 会误判"已读"；且跨连接重复消息无法去重）
  let maxOutSeq = -1, maxInSeq = -1;
  const hist = store.messages[peerId] || [];
  for(const mm of hist){
    if(typeof mm.seq === 'number'){
      if(mm.dir === 'out') maxOutSeq = Math.max(maxOutSeq, mm.seq);
      else if(mm.dir === 'in') maxInSeq = Math.max(maxInSeq, mm.seq);
    }
  }
  connections.set(peerId, {chat: chatCh, file: fileCh, pc, outSeq: maxOutSeq+1, inSeq: maxInSeq+1, pending:new Map()});
  revivable.delete(peerId); peerBye.delete(peerId); cancelAutoRevive(peerId);
  autoReviveRetries.delete(peerId); // 连接成功，清零自动恢复重试计数
  if(pendingPC===pc) pendingPC=null;
  pendingChannel=null;
  clearConnectWatchdog();
  c.lastSeen = nowTs();
  if(pendingPeerIps && pendingPeerIps.length){ c.peerIps = pendingPeerIps; }
  pendingPeerIps = null;
  detectPeerIp(pc, peerId);
  saveStore();
  closeDialog('dlgConnect');
  closeDialog('dlgQr');       // 连接成功自动关闭二维码展示弹窗（应答码/邀请码）
  closeDialog('dlgQrLarge');
  // 首次连接：记录 lastReadTs 作为分界线基准。重连时保留旧值，
  // 确保对方离线消息到达后 m.ts > lastReadTs 能正确触发分界线
  const hadLastRead = !!c.lastReadTs;
  selectContact(peerId, hadLastRead);
  if(!hadLastRead) c.lastReadTs = nowTs();
  if(!oldId) appendSys(peerId, "✅ 已建立加密直连");
  toast("已连接 "+contactDisplayText(c));
  startHeartbeat(peerId); // 启动心跳保活
  // 自动发送离线期间排队的消息
  flushPendingMessages(peerId);
}
function currentConnId(){ // 当前选中且已连接
  if(currentId && connections.has(currentId)) return currentId;
  return null;
}
function onChannelClose(channel){
  const info = channelMap.get(channel); if(!info) return;
  const cId = info.contactId;
  const pc = info.pc;
  channelMap.delete(channel);
  if(!cId) return;
  const conn = connections.get(cId);
  if(!conn) return;
  // 断开当前通道
  if(info.isChat && conn.chat===channel) conn.chat = null;
  else if(!info.isChat && conn.file===channel) conn.file = null;
  // 两个通道都断开才算真正断开
  if(!conn.chat && !conn.file){
    // 清理 pending 定时器与心跳
    for(const [seq, p] of conn.pending) clearTimeout(p.timer);
    conn.pending.clear();
    stopHeartbeat(conn);
    connections.delete(cId);
    // 保留底层 PC 以便尝试免交换码恢复
    if(pc && pc.iceConnectionState!=='closed'){ revivable.set(cId, pc); }
    if(cId===currentId){ appendSys(cId,"连接已断开"); renderChat(); }
    renderContacts();
    if(revivable.has(cId) && !peerBye.has(cId) && !autoReviveTimers.has(cId)){
      scheduleAutoRevive(cId);
    }
  }
}
function scheduleAutoRevive(cId, immediate){
  cancelAutoRevive(cId);
  // immediate：visibilitychange 恢复前台时立即探测（墓碑恢复后 ICE 可能仍存活）。
  // 否则 2.5~4.5s 随机抖动，降低双方同时触发；重试时按次数指数退避。
  let delay;
  if(immediate){ delay = 300; }
  else{
    const retries = autoReviveRetries.get(cId) || 0;
    const base = 2500 + Math.floor(Math.random()*2000);
    delay = base * Math.pow(1.7, retries); // 退避：~3.5s → ~6s → ~10s → ~17s
  }
  const t = setTimeout(async ()=>{
    autoReviveTimers.delete(cId);
    if(connections.has(cId)) return; // 已恢复或已重连
    if(!revivable.has(cId)) return;
    const pc = revivable.get(cId);
    const st = pc.iceConnectionState;
    if(st==='closed' || st==='failed'){ revivable.delete(cId); return; } // ICE 已失效，放弃
    if(!immediate) appendSys(cId, "↻ 正在尝试自动恢复连接…");
    const ok = await attemptRevive(cId);
    if(ok) return; // 成功，finalizeChannels 会接管（清零重试计数）
    // 失败但 PC 仍可能恢复（disconnected）：指数退避重试，上限 4 次（覆盖墓碑恢复后 ICE 缓慢恢复的窗口）
    if(revivable.has(cId) && !peerBye.has(cId) && !connections.has(cId)){
      const retries = (autoReviveRetries.get(cId) || 0) + 1;
      autoReviveRetries.set(cId, retries);
      if(retries < 4){
        scheduleAutoRevive(cId);
      }else if(cId===currentId){
        appendSys(cId, "自动恢复失败，可点「⚡ 重连」手动交换连接码");
        renderChat();
      }
    }else if(cId===currentId && !revivable.has(cId)){
      appendSys(cId, "自动恢复失败，可点「⚡ 重连」手动交换连接码");
      renderChat();
    }
  }, delay);
  autoReviveTimers.set(cId, t);
}
function cancelAutoRevive(cId){
  const t=autoReviveTimers.get(cId);
  if(t){ clearTimeout(t); autoReviveTimers.delete(cId); }
}
function cleanupPending(){
  clearConnectWatchdog();
  if(pendingPC){
    // 清理 pendingPC 上的所有通道
    for(const [ch,info] of channelMap){ if(info.pc===pendingPC){ try{ch.close();}catch(e){} channelMap.delete(ch); } }
    try{ pendingPC.close(); }catch(e){}
    pendingPC=null;
  }
  pendingChannel=null;
  pendingPeerIps=null;
}
async function detectPeerIp(pc, contactId){
  try{
    await new Promise(r=>setTimeout(r,500));
    const stats = await pc.getStats();
    let ip="", ctype="";
    stats.forEach(r=>{
      if(r.type==='candidate-pair' && r.selected){
        const rem = stats.get(r.remoteCandidateId);
        if(rem){
          if(rem.address) ip = rem.address; else if(rem.ip) ip = rem.ip;
          ctype = rem.candidateType || ''; // host / srflx / prflx / relay
        }
      }
    });
    // mDNS 混淆下 getStats 可能拿到 *.local：回退用信令里对端真实 IP 显示，并标记 ipType='signal'
    if(!ip || ip.endsWith('.local')){
      const c0=getContact(contactId);
      const sig = c0 && c0.peerIps && c0.peerIps.find(isRealIp);
      if(sig){ ip=sig; ctype='signal'; }
    }
    if(ip){
      const c=getContact(contactId);
      if(c){ c.ip=ip; c.ipType=ctype; c.lastSeen=nowTs(); saveStore(); renderContacts(); if(contactId===currentId){ renderTopbar(); if(document.getElementById('dIpInfo')) renderDetailIpInfo(c); } }
    }
  }catch(e){}
}
function ipModeLabel(ctype){
  // 仅直连模式：host/prflx 为直连；开启 STUN 辅助时可能出现 srflx；signal 为信令回退显示
  if(ctype==='host'||ctype==='prflx') return '直连';
  if(ctype==='srflx') return 'STUN';
  if(ctype==='signal') return '信令';
  return ctype||'';
}

/* ===================== 已读回执 / ACK ===================== */
function sendReadReceipt(contactId){
  const conn = connections.get(contactId);
  if(!conn || !conn.chat) return;
  const ts = nowTs();
  // 附带已收到的最大 seq，使对端能精确标记"已读"
  const payload = {type:"read", ts};
  if(conn.inSeq > 0) payload.seq = conn.inSeq - 1;
  try{ conn.chat.send(JSON.stringify(payload)); }catch(e){}
}
function sendDeliveredReceipt(contactId){
  const conn = connections.get(contactId);
  if(!conn || !conn.chat) return;
  const ts = nowTs();
  try{ conn.chat.send(JSON.stringify({type:"delivered", ts})); }catch(e){}
}
function sendAck(cId, seq){
  const conn = connections.get(cId);
  if(!conn || !conn.chat) return;
  try{ conn.chat.send(JSON.stringify({type:"ack", seq})); }catch(e){}
}
function retransmitMsg(cId, seq){
  const conn = connections.get(cId);
  if(!conn || !conn.chat) return; // 通道已关闭则停止重传
  const p = conn.pending.get(seq);
  if(!p) return; // 已被 ACK 确认
  p.retries++;
  // 先判断是否已达上限（3次），避免多设一轮 24s 定时器导致延迟 45s 才报失败
  if(p.retries >= 3){
    conn.pending.delete(seq);
    if(cId===currentId) appendSys(cId, "⚠ 消息发送失败（已重试3次）");
    return;
  }
  try{ conn.chat.send(JSON.stringify({type:"msg", ts:p.ts, text:p.text, seq})); }catch(e){}
  p.timer = setTimeout(()=>retransmitMsg(cId, seq), 3000 * Math.pow(2, p.retries));
}
function refreshMessageReadStatus(contactId){
  const c = getContact(contactId);
  if(!c) return;
  const msgs = document.getElementById('messages').querySelectorAll('.read-tag');
  msgs.forEach(rd=>{
    const ds = rd.getAttribute('data-seq');
    if(ds !== null && ds !== ''){
      // 文字消息：用 seq 精确判断（消除时间戳近似的误标）
      const s = parseInt(ds);
      if(typeof c.peerReadSeq==='number' && c.peerReadSeq >= 0 && s <= c.peerReadSeq){ rd.textContent='✓已读'; }
      else if(typeof c.peerDeliveredSeq==='number' && c.peerDeliveredSeq >= 0 && s <= c.peerDeliveredSeq){ rd.textContent='✓已送达'; }
    } else {
      // 文件/图片：无 seq，回退时间戳判断
      const ts = parseInt(rd.getAttribute('data-ts'));
      if(c.peerReadTs && ts <= c.peerReadTs){ rd.textContent='✓已读'; }
      else if(c.peerDeliveredTs && ts <= c.peerDeliveredTs){ rd.textContent='✓已送达'; }
    }
  });
}

/* 发送消息 */
function sendMsg(){
  const ta=document.getElementById('inputMsg');
  const text=ta.value.trim(); if(!text) return;
  const cId=currentId; // 用 currentId 允许离线发送
  if(!cId) return toast("请先选择联系人");
  const conn = connections.get(cId);
  const online = conn && conn.chat;
  // 离线：标记 pending，等连接恢复后自动发送
  if(!online){
    const ts=nowTs();
    addPendingMessage(cId, 'out', text, ts);
    ta.value='';
    return;
  }
  // 在线：正常发送
  if(conn.chat.bufferedAmount > 64*1024) return toast("网络拥塞，稍后重试");
  const ts=nowTs();
  const seq = conn.outSeq++;
  const msg = {type:"msg", ts, text, seq};
  try{ conn.chat.send(JSON.stringify(msg)); }catch(e){ return toast("发送失败: "+e.message); }
  // 加入重传队列（3s 后若未收到 ACK 则重发）
  const timer = setTimeout(()=>retransmitMsg(cId, seq), 3000);
  conn.pending.set(seq, {text, ts, timer, retries:0});
  addMessage(cId,'out',text,ts,seq); // 正常消息带 seq（用于精确回执）
  ta.value='';
}
function addPendingMessage(contactId, dir, text, ts){
  if(!store.messages[contactId]) store.messages[contactId]=[];
  store.messages[contactId].push({ts, dir, text, pending:true});
  saveStore();
  if(contactId===currentId) renderMessages();
  renderContacts();
}
/* 连接建立后，自动发送所有离线期间排队的消息 */
function flushPendingMessages(contactId){
  const conn = connections.get(contactId);
  if(!conn || !conn.chat) return;
  const arr = store.messages[contactId]||[];
  let flushed = false;
  for(const m of arr){
    if(m.pending && m.dir==='out'){
      flushed = true;
      const seq = conn.outSeq++;
      try{ conn.chat.send(JSON.stringify({type:"msg", ts:m.ts, text:m.text, seq})); }catch(e){ continue; }
      const timer = setTimeout(()=>retransmitMsg(contactId, seq), 3000);
      conn.pending.set(seq, {text:m.text, ts:m.ts, timer, retries:0});
      m.seq = seq; // 持久化 seq，用于精确回执判断
      delete m.pending;
    }
  }
  if(flushed){
    saveStore();
    if(contactId===currentId) renderMessages();
    appendSys(contactId, "↻ 已自动发送离线消息");
  }
}
function addMessage(contactId, dir, text, ts, seq){
  const item = {ts:ts||nowTs(), dir, text};
  if(typeof seq==='number') item.seq = seq;
  if(!store.messages[contactId]) store.messages[contactId]=[];
  store.messages[contactId].push(item);
  const c=getContact(contactId); if(c) c.lastSeen=ts||nowTs();
  if(dir==='in' && contactId!==currentId){ store.unread[contactId]=(store.unread[contactId]||0)+1; }
  saveStore();
  if(contactId===currentId) renderMessages();
  renderContacts();
}
function appendSys(contactId, text){
  if(!store.messages[contactId]) store.messages[contactId]=[];
  store.messages[contactId].push({ts:nowTs(), dir:'sys', text});
  saveStore();
  if(contactId===currentId) renderMessages();
}

/* ===================== 文件传输 ===================== */
const FILE_CHUNK = 16*1024;            // 16KB 分块（兼容 SCTP 默认消息上限）
const FILE_BUF_HIGH = 8*1024*1024;     // 背压高水位 8MB
/* 背压等待：缓冲降到低水位以下 / 通道关闭 / 超时 时 resolve。
   通道关闭 resolve（不 reject）——调用方 while 检查 readyState 自行退出循环。 */
function backpressureWait(channel, timeoutMs){
  return new Promise((resolve, reject)=>{
    if(channel.bufferedAmount <= FILE_BUF_HIGH || channel.readyState!=='open'){ resolve(); return; }
    const tm = setTimeout(()=>{ cleanup(); reject(new Error('背压超时')); }, timeoutMs);
    const onLow = ()=>{ cleanup(); resolve(); };
    const onClose = ()=>{ cleanup(); resolve(); };
    const cleanup = ()=>{
      clearTimeout(tm);
      channel.removeEventListener('bufferedamountlow', onLow);
      channel.removeEventListener('close', onClose);
      channel.removeEventListener('error', onClose);
    };
    channel.addEventListener('bufferedamountlow', onLow);
    channel.addEventListener('close', onClose);
    channel.addEventListener('error', onClose);
  });
}
/* file 通道传输串行锁：同一 file 通道上避免多个传输并发，导致分块交错（接收端 chunks 数组
   混合，文件/图片损坏）。全局单锁——file 通道同一时刻只跑一个传输，后续排队等候。 */
let _fileLock = Promise.resolve();
function acquireFileLock(){
  const prev = _fileLock;
  let release;
  _fileLock = new Promise(r=>{ release = r; });
  return prev.then(()=>release);
}
const fileTransfers = new Map();       // fid -> {received,size,dir,contactId,name} 进度（出/入共用）
const fileUrls = new Map();            // fid -> objectURL（运行时下载链接，不持久化）

function pickFile(){ document.getElementById('fileSendInput').click(); }
/* 附件菜单：聚合 拍照/图片/视频/录像/文件 到「＋」按钮 */
function toggleAttachMenu(e){
  e && e.stopPropagation();
  if(!currentId){ toast("请先选择联系人"); return; }
  if(!connections.has(currentId)){ toast("未连接，无法发送图片/视频/文件，请先重连"); return; }
  document.getElementById('attachPop').classList.toggle('show');
}
function closeAttachMenu(){ document.getElementById('attachPop').classList.remove('show'); }
document.getElementById('attachPop').addEventListener('click', e=>{ // 选中任一项后关闭
  if(e.target.closest('button')) closeAttachMenu();
});
document.addEventListener('click', ()=>closeAttachMenu()); // 点外部关闭

/* 图片查看器：页内放大/缩小/拖动，替代 window.open（iOS 不响应、安卓/PC 开新标签页） */
let ivScale=1, ivX=0, ivY=0, ivMoved=false, ivClickTimer=null;
function ivApply(){
  const img=document.getElementById('ivImg');
  if(img) img.style.transform=`translate(${ivX}px, ${ivY}px) scale(${ivScale})`;
}
function openImageview(src){
  if(!src) return;
  ivScale=1; ivX=0; ivY=0; ivMoved=false;
  clearTimeout(ivClickTimer);
  const img=document.getElementById('ivImg');
  img.src=src;
  ivApply();
  document.getElementById('dlgImageview').classList.add('show');
}
function closeImageview(){ clearTimeout(ivClickTimer); document.getElementById('dlgImageview').classList.remove('show'); }
function ivZoom(dir){
  ivScale = Math.max(1, Math.min(5, +(ivScale + dir*0.3).toFixed(2)));
  if(ivScale<=1){ ivScale=1; ivX=0; ivY=0; }
  ivApply();
}
function ivReset(){ ivScale=1; ivX=0; ivY=0; ivApply(); }
(function(){
  const ov=document.getElementById('dlgImageview');
  const img=document.getElementById('ivImg');
  if(!ov || !img) return;
  ov.addEventListener('click', e=>{
    if(ivMoved){ ivMoved=false; return; } // 拖动/pinch 后的合成 click 不关闭
    if(e.target===ov || e.target.classList.contains('iv-stage')){ closeImageview(); return; } // 点背景关闭
    if(e.target===img){
      // 点图片：延迟关闭，留出双击缩放窗口；放大状态下点图片不关闭（避免误关，用背景/叉号关闭）
      clearTimeout(ivClickTimer);
      ivClickTimer=setTimeout(()=>{ if(ivScale<=1) closeImageview(); }, 250);
    }
  });
  img.addEventListener('dblclick', e=>{ e.stopPropagation(); clearTimeout(ivClickTimer); ivScale = ivScale>=2.5 ? 1 : 2.5; if(ivScale===1){ivX=0;ivY=0;} ivApply(); });
  ov.addEventListener('wheel', e=>{ e.preventDefault(); ivZoom(e.deltaY<0?1:-1); }, {passive:false});
  // 鼠标拖动平移（PC，放大时）
  let drag=null;
  img.addEventListener('mousedown', e=>{ if(ivScale>1){ e.preventDefault(); drag={x:e.clientX,y:e.clientY,ox:ivX,oy:ivY}; ivMoved=false; } });
  window.addEventListener('mousemove', e=>{ if(drag){ ivX=drag.ox+(e.clientX-drag.x); ivY=drag.oy+(e.clientY-drag.y); ivApply(); ivMoved=true; } });
  window.addEventListener('mouseup', ()=>{ drag=null; });
  // 触摸：单指拖动（放大时）+ 双指 pinch 缩放
  const tdist=t=>Math.hypot(t[0].clientX-t[1].clientX, t[0].clientY-t[1].clientY);
  let touch=null;
  img.addEventListener('touchstart', e=>{
    if(e.touches.length===2){
      touch={mode:'pinch', d0:tdist(e.touches), s0:ivScale};
      e.preventDefault();
    }else if(e.touches.length===1 && ivScale>1){
      touch={mode:'pan', x:e.touches[0].clientX, y:e.touches[0].clientY, ox:ivX, oy:ivY};
      ivMoved=false;
    }
  }, {passive:false});
  img.addEventListener('touchmove', e=>{
    if(!touch) return;
    if(touch.mode==='pinch' && e.touches.length===2){
      ivScale = Math.max(1, Math.min(5, +(touch.s0 * tdist(e.touches)/touch.d0).toFixed(2)));
      if(ivScale<=1){ ivScale=1; ivX=0; ivY=0; }
      ivApply(); e.preventDefault();
    }else if(touch.mode==='pan' && e.touches.length===1){
      ivX=touch.ox+(e.touches[0].clientX-touch.x);
      ivY=touch.oy+(e.touches[0].clientY-touch.y);
      ivApply(); ivMoved=true; e.preventDefault();
    }
  }, {passive:false});
  img.addEventListener('touchend', e=>{
    if(e.touches.length===0){ touch=null; }
    else if(e.touches.length===1 && touch && touch.mode==='pinch'){
      // 双指变单指：转为平移基线
      touch={mode:'pan', x:e.touches[0].clientX, y:e.touches[0].clientY, ox:ivX, oy:ivY};
      ivMoved=false;
    }
  });
})();

document.getElementById('fileSendInput').addEventListener('change', e=>{
  try{
    const f=e.target.files[0]; e.target.value=''; if(!f) return;
    sendFile(f).catch(err=>{ console.error('sendFile:',err); toast('文件发送异常'); });
  }catch(err){ console.error('file input:',err); toast('操作失败'); }
});
/* 图片发送 input 监听 */
document.getElementById('imageSendInput').addEventListener('change', e=>{
  try{
    const f=e.target.files[0]; e.target.value=''; if(!f) return;
    sendImage(f).catch(err=>{ console.error('sendImage:',err); toast('图片发送异常'); });
  }catch(err){ console.error('image input:',err); toast('操作失败'); }
});
/* 相机拍照发送 input 监听（capture=environment，移动端直接调起后置相机） */
document.getElementById('cameraInput').addEventListener('change', e=>{
  try{
    const f=e.target.files[0]; e.target.value=''; if(!f) return;
    sendImage(f).catch(err=>{ console.error('sendImage:',err); toast('图片发送异常'); });
  }catch(err){ console.error('camera input:',err); toast('操作失败'); }
});
function fmtSize(n){
  if(n<1024) return n+' B';
  if(n<1048576) return (n/1024).toFixed(1)+' KB';
  if(n<1073741824) return (n/1048576).toFixed(1)+' MB';
  return (n/1073741824).toFixed(2)+' GB';
}
async function sendFile(file){
  const cId=currentConnId();
  const conn = connections.get(cId);
  if(!conn || !conn.file || conn.file.readyState!=='open') return toast("未连接，无法发送文件");
  const channel=conn.file;
  if(!channel.bufferedAmountLowThreshold || channel.bufferedAmountLowThreshold<1*1024*1024) channel.bufferedAmountLowThreshold=1*1024*1024;
  const fid=randId();
  const meta={type:"file-meta", fid, name:file.name, size:file.size, mime:file.type||'application/octet-stream'};
  /* meta / 分块 / end 全部走同一 file 通道（同一 SCTP ordered stream），确保 end 严格在所有分块
     之后到达。旧版 meta/end 走 chat 通道，公网高延迟下 chat 通道的 end 会先于 file 通道尾部分块
     到达，导致接收方用不完整 chunks 拼 Blob，文件残缺。串行锁防止并发传输分块交错。 */
  const release = await acquireFileLock();
  try{
    try{ channel.send(JSON.stringify(meta)); }catch(e){ return toast("发送失败: "+e.message); }
    fileTransfers.set(fid,{received:0,size:file.size,dir:'out',contactId:cId,name:file.name});
    addFileMessage(cId,'out',meta);
    let offset=0;
    while(offset<file.size && channel.readyState==='open'){
      const buf=await file.slice(offset, offset+FILE_CHUNK).arrayBuffer();
      // 背压：缓冲过高时等 bufferedamountlow 事件（带超时 + 通道关闭检测）
      if(channel.bufferedAmount > FILE_BUF_HIGH){
        try{ await backpressureWait(channel, 30000); }catch(e){ toast("传输中断：网络拥塞超时"); break; }
      }
      if(channel.readyState!=='open') break;
      channel.send(buf);
      offset+=buf.byteLength;
      const st=fileTransfers.get(fid); if(st){ st.received=offset; updateFileProgress(fid); }
    }
    if(offset>=file.size){ try{ channel.send(JSON.stringify({type:"file-end", fid})); }catch(e){} }
  }catch(e){ toast("文件发送失败: "+e.message); }
  finally{ fileTransfers.delete(fid); release(); }
}
function startReceiveFile(cId, info, m){
  info.incomingFile={fid:m.fid, name:m.name, size:m.size, mime:m.mime, received:0, chunks:[]};
  fileTransfers.set(m.fid,{received:0,size:m.size,dir:'in',contactId:cId,name:m.name});
  addFileMessage(cId,'in',m);
}
function finishReceiveFile(cId, info, fid){
  const inc=info.incomingFile; info.incomingFile=null;
  fileTransfers.delete(fid);
  if(!inc || inc.fid!==fid) return;
  const blob=new Blob(inc.chunks,{type:inc.mime||'application/octet-stream'});
  fileUrls.set(fid, URL.createObjectURL(blob));
  if(cId===currentId){
    const el=document.getElementById('file-'+fid);
    if(el) renderFileCardInto(el,{fid,name:inc.name,size:inc.size,dir:'in'});
  }
}
function addFileMessage(contactId, dir, meta){
  if(!store.messages[contactId]) store.messages[contactId]=[];
  const item={ts:nowTs(), dir, file:{fid:meta.fid, name:meta.name, size:meta.size}};
  store.messages[contactId].push(item);
  const c=getContact(contactId); if(c) c.lastSeen=item.ts;
  if(dir==='in' && contactId!==currentId){ store.unread[contactId]=(store.unread[contactId]||0)+1; }
  saveStore();
  if(contactId===currentId) renderMessages();
  renderContacts();
}
function renderFileCardInto(el, f){
  const st=fileTransfers.get(f.fid);
  const url=fileUrls.get(f.fid);
  const transferring=!!st;
  const pct = st && st.size ? Math.min(100, Math.round(st.received/st.size*100)) : 0;
  let right='';
  if(url){ right=`<a href="${url}" download="${escapeHtml(f.name)}">下载</a>`; }
  else if(f.dir==='out' && !transferring){ right=`<span class="fs">已发送</span>`; }
  else if(f.dir==='in' && !transferring){ right=`<span class="fs">（已失效）</span>`; }
  const info = transferring
    ? `<div class="fs"><span class="fl-pct">${pct}%</span> · ${fmtSize(st.received)}/${fmtSize(f.size)}</div><div class="prog"><i style="width:${pct}%"></i></div>`
    : `<div class="fs">${fmtSize(f.size)}</div>`;
  const readTag = f.dir==='out' && f.ts ? `<span class="read-tag" data-ts="${f.ts}"></span>` : '';
  el.innerHTML=`<div class="file-card"><span class="fi">📎</span><div class="fc-info"><div class="fn">${escapeHtml(f.name)}</div>${info}</div><div>${right}${readTag}</div></div>`;
}
function updateFileProgress(fid){
  const st=fileTransfers.get(fid); if(!st) return;
  if(st.contactId!==currentId) return;
  const el=document.getElementById('file-'+fid); if(!el) return;
  const pct = st.size ? Math.min(100, Math.round(st.received/st.size*100)) : 100;
  const prog=el.querySelector('.prog>i'); if(prog) prog.style.width=pct+'%';
  const lp=el.querySelector('.fl-pct'); if(lp) lp.textContent=pct+'%';
}

/* ===================== 图片传输（内嵌显示） ===================== */
const imageTransfers = new Map();  // iid -> {received,size,dir,contactId,name}（同 fileTransfers 模式）
const imageUrls = new Map();       // iid -> objectURL（运行时，不持久化）

function pickImage(){ document.getElementById('imageSendInput').click(); }
function pickCamera(){ document.getElementById('cameraInput').click(); }
async function sendImage(file){
  if(!file.type.startsWith('image/')) return toast("请选择图片文件");
  const cId=currentConnId();
  const conn = connections.get(cId);
  if(!conn || !conn.file || conn.file.readyState!=='open') return toast("未连接，无法发送图片");
  const channel=conn.file;
  if(!channel.bufferedAmountLowThreshold || channel.bufferedAmountLowThreshold<1*1024*1024) channel.bufferedAmountLowThreshold=1*1024*1024;
  const iid=randId();
  const meta={type:"image-meta", iid, name:file.name, size:file.size, mime:file.type||'image/png'};
  /* meta / 分块 / end 全部走同一 file 通道（同一 SCTP ordered stream），确保 end 不会抢先于
     分块到达——旧版 end 走 chat 通道，公网高延迟下会先于 file 通道尾部分块到达，接收方用不完整
     chunks 拼 Blob，图片出现顶部一条/灰色条带等残缺。串行锁防止并发传输分块交错。 */
  const release = await acquireFileLock();
  try{
    try{ channel.send(JSON.stringify(meta)); }catch(e){ return toast("发送失败: "+e.message); }
    imageTransfers.set(iid,{received:0,size:file.size,dir:'out',contactId:cId,name:file.name});
    imageUrls.set(iid, URL.createObjectURL(file)); // 发送方立即显示缩略图
    addImageMessage(cId,'out',meta);
    let offset=0;
    while(offset<file.size && channel.readyState==='open'){
      const buf=await file.slice(offset, offset+FILE_CHUNK).arrayBuffer();
      if(channel.bufferedAmount > FILE_BUF_HIGH){
        try{ await backpressureWait(channel, 30000); }catch(e){ toast("传输中断：网络拥塞超时"); break; }
      }
      if(channel.readyState!=='open') break;
      channel.send(buf);
      offset+=buf.byteLength;
      const st=imageTransfers.get(iid); if(st){ st.received=offset; updateImageProgress(iid); }
    }
    if(offset>=file.size){ try{ channel.send(JSON.stringify({type:"image-end", iid})); }catch(e){} }
  }catch(e){ toast("图片发送失败: "+e.message); }
  finally{ imageTransfers.delete(iid); release(); }
}
function startReceiveImage(cId, info, m){
  info.incomingImage={iid:m.iid, name:m.name, size:m.size, mime:m.mime, received:0, chunks:[]};
  imageTransfers.set(m.iid,{received:0,size:m.size,dir:'in',contactId:cId,name:m.name});
  addImageMessage(cId,'in',m);
}
function finishReceiveImage(cId, info, iid){
  const inc=info.incomingImage; info.incomingImage=null;
  imageTransfers.delete(iid);
  if(!inc || inc.iid!==iid) return;
  const blob=new Blob(inc.chunks,{type:inc.mime||'image/png'});
  imageUrls.set(iid, URL.createObjectURL(blob));
  if(cId===currentId){
    const el=document.getElementById('img-'+iid);
    if(el) renderImageInto(el,{iid,name:inc.name,size:inc.size,dir:'in'});
  }
}
function addImageMessage(contactId, dir, meta){
  if(!store.messages[contactId]) store.messages[contactId]=[];
  const item={ts:nowTs(), dir, image:{iid:meta.iid, name:meta.name, size:meta.size}};
  store.messages[contactId].push(item);
  const c=getContact(contactId); if(c) c.lastSeen=item.ts;
  if(dir==='in' && contactId!==currentId){ store.unread[contactId]=(store.unread[contactId]||0)+1; }
  saveStore();
  if(contactId===currentId) renderMessages();
  renderContacts();
}
function renderImageInto(el, img){
  const url=imageUrls.get(img.iid);
  const st=imageTransfers.get(img.iid);
  const transferring=!!st;
  let body='';
  if(url){
    body=`<img src="${url}" alt="${escapeHtml(img.name)}" onclick="openImageview(this.src)" title="点击查看原图">`;
  }else if(transferring){
    const pct = st && st.size ? Math.min(100, Math.round(st.received/st.size*100)) : 0;
    body=`<div class="img-expired"><div style="text-align:center"><span class="spinner" style="margin-right:6px"></span>${pct}%</div></div>`;
  }else{
    body=`<div class="img-expired">（图片已失效 · ${fmtSize(img.size)}）</div>`;
  }
  const readTag = img.dir==='out' && img.ts ? `<span class="read-tag" data-ts="${img.ts}"></span>` : '';
  el.innerHTML=body+`<div class="img-info">${fmtTime(img.ts||nowTs())}${readTag}</div>`;
}
function updateImageProgress(iid){
  const st=imageTransfers.get(iid); if(!st) return;
  if(st.contactId!==currentId) return;
  const el=document.getElementById('img-'+iid); if(!el) return;
  const pct = st.size ? Math.min(100, Math.round(st.received/st.size*100)) : 100;
  const exp=el.querySelector('.img-expired>div');
  if(exp) exp.textContent=pct+'%';
}

/* ===================== 视频传输（内嵌播放，同 image 模式） ===================== */
const videoTransfers = new Map();  // vid -> {received,size,dir,contactId,name}（同 imageTransfers 模式）
const videoUrls = new Map();       // vid -> objectURL（运行时，不持久化）

function pickVideo(){ document.getElementById('videoSendInput').click(); }
function pickVideoCamera(){ document.getElementById('videoCameraInput').click(); }
// iOS Safari 下 input[capture] 直接调起相机录像，Safari 后台时易被系统回收导致整个浏览器闪退
// （相机占内存 + 已有 WebRTC 连接占内存）。改走系统选择器（用户仍可选"录像"），Safari 不立即
// 后台，降低闪退概率；安卓保留 capture 直接调起后置相机。
(function(){
  const isIOS = /iPad|iPhone|iPod/.test(navigator.userAgent) || (navigator.platform==='MacIntel' && navigator.maxTouchPoints>1);
  if(isIOS){
    const vci=document.getElementById('videoCameraInput');
    if(vci) vci.removeAttribute('capture');
  }
})();
async function sendVideo(file){
  if(!file.type.startsWith('video/')) return toast("请选择视频文件");
  if(file.size > 100*1024*1024) return toast("视频过大（>100MB），请缩短或压缩后再发，以免接收端内存溢出");
  const cId=currentConnId();
  const conn = connections.get(cId);
  if(!conn || !conn.file || conn.file.readyState!=='open') return toast("未连接，无法发送视频");
  const channel=conn.file;
  if(!channel.bufferedAmountLowThreshold || channel.bufferedAmountLowThreshold<1*1024*1024) channel.bufferedAmountLowThreshold=1*1024*1024;
  const vid=randId();
  const meta={type:"video-meta", vid, name:file.name, size:file.size, mime:file.type||'video/mp4'};
  /* meta/分块/end 全走同一 file 通道（同 image），串行锁防并发分块交错 */
  const release = await acquireFileLock();
  try{
    try{ channel.send(JSON.stringify(meta)); }catch(e){ return toast("发送失败: "+e.message); }
    videoTransfers.set(vid,{received:0,size:file.size,dir:'out',contactId:cId,name:file.name});
    videoUrls.set(vid, URL.createObjectURL(file)); // 发送方立即显示
    addVideoMessage(cId,'out',meta);
    let offset=0;
    while(offset<file.size && channel.readyState==='open'){
      const buf=await file.slice(offset, offset+FILE_CHUNK).arrayBuffer();
      if(channel.bufferedAmount > FILE_BUF_HIGH){
        try{ await backpressureWait(channel, 30000); }catch(e){ toast("传输中断：网络拥塞超时"); break; }
      }
      if(channel.readyState!=='open') break;
      channel.send(buf);
      offset+=buf.byteLength;
      const st=videoTransfers.get(vid); if(st){ st.received=offset; updateVideoProgress(vid); }
    }
    if(offset>=file.size){ try{ channel.send(JSON.stringify({type:"video-end", vid})); }catch(e){} }
  }catch(e){ toast("视频发送失败: "+e.message); }
  finally{ videoTransfers.delete(vid); release(); }
}
function startReceiveVideo(cId, info, m){
  info.incomingVideo={vid:m.vid, name:m.name, size:m.size, mime:m.mime, received:0, chunks:[]};
  videoTransfers.set(m.vid,{received:0,size:m.size,dir:'in',contactId:cId,name:m.name});
  addVideoMessage(cId,'in',m);
}
function finishReceiveVideo(cId, info, vid){
  const inc=info.incomingVideo; info.incomingVideo=null;
  videoTransfers.delete(vid);
  if(!inc || inc.vid!==vid) return;
  const blob=new Blob(inc.chunks,{type:inc.mime||'video/mp4'});
  videoUrls.set(vid, URL.createObjectURL(blob));
  if(cId===currentId){
    const el=document.getElementById('vid-'+vid);
    if(el) renderVideoInto(el,{vid,name:inc.name,size:inc.size,dir:'in'});
  }
}
function addVideoMessage(contactId, dir, meta){
  if(!store.messages[contactId]) store.messages[contactId]=[];
  const item={ts:nowTs(), dir, video:{vid:meta.vid, name:meta.name, size:meta.size}};
  store.messages[contactId].push(item);
  const c=getContact(contactId); if(c) c.lastSeen=item.ts;
  if(dir==='in' && contactId!==currentId){ store.unread[contactId]=(store.unread[contactId]||0)+1; }
  saveStore();
  if(contactId===currentId) renderMessages();
  renderContacts();
}
function renderVideoInto(el, v){
  const url=videoUrls.get(v.vid);
  const st=videoTransfers.get(v.vid);
  const transferring=!!st;
  let body='';
  if(url){
    body=`<video controls preload="metadata" src="${url}" title="${escapeHtml(v.name)}"></video>`;
  }else if(transferring){
    const pct = st && st.size ? Math.min(100, Math.round(st.received/st.size*100)) : 0;
    body=`<div class="img-expired"><div style="text-align:center"><span class="spinner" style="margin-right:6px"></span>${pct}%</div></div>`;
  }else{
    body=`<div class="img-expired">（视频已失效 · ${fmtSize(v.size)}）</div>`;
  }
  const readTag = v.dir==='out' && v.ts ? `<span class="read-tag" data-ts="${v.ts}"></span>` : '';
  el.innerHTML=body+`<div class="img-info">${fmtTime(v.ts||nowTs())}${readTag}</div>`;
}
function updateVideoProgress(vid){
  const st=videoTransfers.get(vid); if(!st) return;
  if(st.contactId!==currentId) return;
  const el=document.getElementById('vid-'+vid); if(!el) return;
  const pct = st.size ? Math.min(100, Math.round(st.received/st.size*100)) : 100;
  const exp=el.querySelector('.img-expired>div');
  if(exp) exp.textContent=pct+'%';
}
/* 视频 input 监听（本地选 / 相机录像，capture=environment 移动端调起后置相机） */
document.getElementById('videoSendInput').addEventListener('change', e=>{
  try{
    const f=e.target.files[0]; e.target.value=''; if(!f) return;
    sendVideo(f).catch(err=>{ console.error('sendVideo:',err); toast('视频发送异常'); });
  }catch(err){ console.error('video input:',err); toast('操作失败'); }
});
document.getElementById('videoCameraInput').addEventListener('change', e=>{
  try{
    const f=e.target.files[0]; e.target.value=''; if(!f) return;
    sendVideo(f).catch(err=>{ console.error('sendVideo:',err); toast('视频发送异常'); });
  }catch(err){ console.error('video camera input:',err); toast('操作失败'); }
});

/* ===================== 语音消息（按住录音 + 内嵌播放，v2.13.0） ===================== */
const audioTransfers = new Map();  // aid -> {received,size,dir,contactId,name}（同 image/video 模式）
const audioUrls = new Map();       // aid -> objectURL（运行时，不持久化）

async function sendAudio(blob){
  const cId=currentConnId();
  const conn = connections.get(cId);
  if(!conn || !conn.file || conn.file.readyState!=='open') return toast("未连接，无法发送语音");
  const channel=conn.file;
  if(!channel.bufferedAmountLowThreshold || channel.bufferedAmountLowThreshold<1*1024*1024) channel.bufferedAmountLowThreshold=1*1024*1024;
  const aid=randId();
  const mime = blob.type || 'audio/webm';
  const meta={type:"audio-meta", aid, name:"voice", size:blob.size, mime};
  /* meta/分块/end 全走同一 file 通道（同 image/video），串行锁防并发分块交错 */
  const release = await acquireFileLock();
  try{
    try{ channel.send(JSON.stringify(meta)); }catch(e){ return toast("发送失败: "+e.message); }
    audioTransfers.set(aid,{received:0,size:blob.size,dir:'out',contactId:cId,name:"voice"});
    audioUrls.set(aid, URL.createObjectURL(blob)); // 发送方立即显示播放器
    addAudioMessage(cId,'out',meta);
    let offset=0;
    while(offset<blob.size && channel.readyState==='open'){
      const buf=await blob.slice(offset, offset+FILE_CHUNK).arrayBuffer();
      if(channel.bufferedAmount > FILE_BUF_HIGH){
        try{ await backpressureWait(channel, 30000); }catch(e){ toast("传输中断：网络拥塞超时"); break; }
      }
      if(channel.readyState!=='open') break;
      channel.send(buf);
      offset+=buf.byteLength;
      const st=audioTransfers.get(aid); if(st){ st.received=offset; updateAudioProgress(aid); }
    }
    if(offset>=blob.size){ try{ channel.send(JSON.stringify({type:"audio-end", aid})); }catch(e){} }
  }catch(e){ toast("语音发送失败: "+e.message); }
  finally{ audioTransfers.delete(aid); release(); }
}
function startReceiveAudio(cId, info, m){
  info.incomingAudio={aid:m.aid, name:m.name, size:m.size, mime:m.mime, received:0, chunks:[]};
  audioTransfers.set(m.aid,{received:0,size:m.size,dir:'in',contactId:cId,name:m.name});
  addAudioMessage(cId,'in',m);
}
function finishReceiveAudio(cId, info, aid){
  const inc=info.incomingAudio; info.incomingAudio=null;
  audioTransfers.delete(aid);
  if(!inc || inc.aid!==aid) return;
  const blob=new Blob(inc.chunks,{type:inc.mime||'audio/webm'});
  audioUrls.set(aid, URL.createObjectURL(blob));
  if(cId===currentId){
    const el=document.getElementById('aud-'+aid);
    if(el) renderAudioInto(el,{aid,name:inc.name,size:inc.size,dir:'in'});
  }
}
function addAudioMessage(contactId, dir, meta){
  if(!store.messages[contactId]) store.messages[contactId]=[];
  const item={ts:nowTs(), dir, audio:{aid:meta.aid, name:meta.name, size:meta.size}};
  store.messages[contactId].push(item);
  const c=getContact(contactId); if(c) c.lastSeen=item.ts;
  if(dir==='in' && contactId!==currentId){ store.unread[contactId]=(store.unread[contactId]||0)+1; }
  saveStore();
  if(contactId===currentId) renderMessages();
  renderContacts();
}
function renderAudioInto(el, a){
  const url=audioUrls.get(a.aid);
  const st=audioTransfers.get(a.aid);
  const transferring=!!st;
  let body='';
  if(url){
    body=`<div class="aud-msg" data-aid="${a.aid}">
      <button class="aud-play" onclick="toggleAudioPlay('${a.aid}')" title="播放/暂停">▶</button>
      <div class="aud-track" onclick="seekAudio('${a.aid}', event)" title="点击定位"><div class="aud-fill" id="audfill-${a.aid}"></div></div>
      <span class="aud-dur" id="auddur-${a.aid}">0:00</span>
    </div>`;
  }else if(transferring){
    const pct = st && st.size ? Math.min(100, Math.round(st.received/st.size*100)) : 0;
    body=`<div class="aud-msg"><span class="spinner" style="margin-right:6px"></span>接收中 ${pct}%</div>`;
  }else{
    body=`<div class="aud-msg aud-expired">语音已失效</div>`;
  }
  const readTag = a.dir==='out' && a.ts ? `<span class="read-tag" data-ts="${a.ts}"></span>` : '';
  el.innerHTML=body+`<div class="img-info">${fmtTime(a.ts||nowTs())}${readTag}</div>`;
}
/* 自定义语音播放器（替代原生 <audio controls>，样式统一、可点击进度条定位） */
const audioPlayers = new Map(); // aid -> HTMLAudioElement
function fmtAudioTime(s){
  if(!s || !isFinite(s)) return '0:00';
  const m=Math.floor(s/60), ss=Math.floor(s%60);
  return m+':'+String(ss).padStart(2,'0');
}
function toggleAudioPlay(aid){
  const url=audioUrls.get(aid); if(!url) return;
  let au=audioPlayers.get(aid);
  if(!au){
    au=new Audio(url); audioPlayers.set(aid, au);
    const sync=()=>{
      const fill=document.getElementById('audfill-'+aid);
      if(fill && au.duration) fill.style.width=(au.currentTime/au.duration*100)+'%';
      const dur=document.getElementById('auddur-'+aid);
      if(dur) dur.textContent=fmtAudioTime(au.duration || au.currentTime);
    };
    au.addEventListener('timeupdate', sync);
    au.addEventListener('loadedmetadata', sync);
    au.addEventListener('ended', ()=>{
      const btn=document.querySelector(`.aud-msg[data-aid="${aid}"] .aud-play`);
      if(btn) btn.textContent='▶';
      const fill=document.getElementById('audfill-'+aid); if(fill) fill.style.width='0%';
    });
  }
  const btn=document.querySelector(`.aud-msg[data-aid="${aid}"] .aud-play`);
  if(au.paused){ au.play().catch(()=>{}); if(btn) btn.textContent='⏸'; }
  else{ au.pause(); if(btn) btn.textContent='▶'; }
}
function seekAudio(aid, e){
  const au=audioPlayers.get(aid); if(!au || !au.duration) return;
  const track=e.currentTarget;
  const rect=track.getBoundingClientRect();
  const ratio=Math.max(0, Math.min(1, (e.clientX-rect.left)/rect.width));
  au.currentTime=ratio*au.duration;
}
function updateAudioProgress(aid){
  const st=audioTransfers.get(aid); if(!st) return;
  if(st.contactId!==currentId) return;
  const el=document.getElementById('aud-'+aid); if(!el) return;
  const pct = st.size ? Math.min(100, Math.round(st.received/st.size*100)) : 100;
  const exp=el.querySelector('.img-expired>div');
  if(exp) exp.textContent=pct+'%';
}

/* 录音：按住话筒开始，松手停止并弹确认弹窗（回放/发送/取消） */
let mediaRecorder=null, recChunks=[], recStream=null, recTimer=null, recStartTs=0, recBlob=null, recMime='', recPending=false, recPressing=false, recReleaseTimer=null;
function startRecord(){
  if(!currentId) return toast("请先选择联系人");
  if(!connections.has(currentId)) return toast("未连接，无法发送语音");
  // iOS Safari 的 MediaRecorder 录音会触发进程级崩溃（无法 try/catch 兜底），禁用并提示
  const isIOS = /iPad|iPhone|iPod/.test(navigator.userAgent) || (navigator.platform==='MacIntel' && navigator.maxTouchPoints>1);
  if(isIOS) return toast("iOS 录音易致浏览器崩溃，请改用 Edge/Chrome 或电脑端录音");
  if(typeof MediaRecorder === 'undefined') return toast("当前浏览器不支持录音");
  if(!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) return toast("麦克风不可用（需 HTTPS 或 localhost）");
  recPressing=true;
  clearTimeout(recReleaseTimer); // 复用窗口内取消释放
  // 立即显示录音指示，权限申请阶段也有反馈（移动端首次需授权，避免按住无反应）
  const ind=document.getElementById('recIndicator');
  const rt=document.getElementById('recTime');
  if(ind) ind.style.display='flex';
  if(rt) rt.textContent='准备中…';
  if(recStream && recStream.active){ beginRec(recStream); return; } // 复用已授权的麦克风，免重复申请
  recPending=true;
  recMime = MediaRecorder.isTypeSupported('audio/webm') ? 'audio/webm' : (MediaRecorder.isTypeSupported('audio/mp4') ? 'audio/mp4' : '');
  navigator.mediaDevices.getUserMedia({audio:true}).then(stream=>{
    recPending=false;
    recStream=stream;
    if(!recPressing){
      // 权限申请期间用户已松手：保留 stream 供下次复用，提示再按一次（不静默丢弃）
      toast("麦克风已就绪，请按住话筒录音");
      if(ind) ind.style.display='none';
      scheduleRecRelease();
      return;
    }
    beginRec(stream);
  }).catch(err=>{
    recPending=false;
    if(ind) ind.style.display='none';
    toast("麦克风不可用：" + (err.message||err.name));
  });
}
function beginRec(stream){
  recChunks=[];
  try{ mediaRecorder = new MediaRecorder(stream, recMime?{mimeType:recMime}:undefined); }
  catch(e){ mediaRecorder = new MediaRecorder(stream); recMime=''; }
  mediaRecorder.ondataavailable = e=>{ if(e.data && e.data.size>0) recChunks.push(e.data); };
  mediaRecorder.onerror = e=>{
    toast("录音出错：" + ((e.error && e.error.message) || ''));
    const ind2=document.getElementById('recIndicator'); if(ind2) ind2.style.display='none';
    if(recTimer){ clearInterval(recTimer); recTimer=null; }
  };
  mediaRecorder.onstop = ()=>{
    recBlob = new Blob(recChunks, {type: (mediaRecorder.mimeType) || recMime || 'audio/webm'});
    if(recBlob.size < 1){ toast("录音为空"); recBlob=null; scheduleRecRelease(); return; }
    const preview=document.getElementById('recPreview');
    if(preview.src) URL.revokeObjectURL(preview.src);
    preview.src = URL.createObjectURL(recBlob);
    document.getElementById('dlgAudioConfirm').classList.add('show');
    scheduleRecRelease(); // 录音结束，延迟释放麦克风
  };
  mediaRecorder.start(250); // timeslice 250ms 分段触发 dataavailable，iOS 某些版本不分段会崩溃
  recStartTs = Date.now();
  document.getElementById('recIndicator').style.display='flex';
  updateRecTime();
  recTimer = setInterval(updateRecTime, 200);
}
function updateRecTime(){
  const s = Math.floor((Date.now()-recStartTs)/1000);
  const mm = String(Math.floor(s/60)).padStart(2,'0');
  const ss = String(s%60).padStart(2,'0');
  const el=document.getElementById('recTime'); if(el) el.textContent = mm+':'+ss;
}
/* 延迟释放麦克风：松手后 10s 内未再录音则关闭 tracks（灭指示灯、释放硬件），
   期间再按住可复用 stream 免重新申请权限。 */
function scheduleRecRelease(){
  clearTimeout(recReleaseTimer);
  recReleaseTimer = setTimeout(()=>{
    if(mediaRecorder && mediaRecorder.state!=='inactive') return; // 仍在录音，跳过
    if(recStream){ recStream.getTracks().forEach(t=>t.stop()); recStream=null; }
  }, 10000);
}
function stopRecord(){
  recPressing=false;
  if(recTimer){ clearInterval(recTimer); recTimer=null; }
  const ind=document.getElementById('recIndicator'); if(ind) ind.style.display='none';
  if(recPending) return; // 权限申请中，等申请结果按 recPressing 处理（不取消）
  if(mediaRecorder && mediaRecorder.state!=='inactive'){ try{ mediaRecorder.stop(); }catch(e){} }
}
function cancelRecordedAudio(){
  const p=document.getElementById('recPreview'); if(p){ if(p.src) URL.revokeObjectURL(p.src); p.src=''; }
  closeDialog('dlgAudioConfirm');
  recBlob=null;
}
async function sendRecordedAudio(){
  if(!recBlob) return;
  const blob=recBlob; recBlob=null;
  const p=document.getElementById('recPreview'); if(p){ if(p.src) URL.revokeObjectURL(p.src); p.src=''; }
  closeDialog('dlgAudioConfirm');
  await sendAudio(blob);
}
/* 话筒按钮：按住录音，松手停止 */
(function(){
  const mic=document.getElementById('btnMic');
  if(!mic) return;
  const rp=document.getElementById('recPreview');
  if(rp) rp.addEventListener('error', ()=>toast("录音回放失败，格式可能不受支持"));
  let pressing=false;
  const down=e=>{ e.preventDefault(); pressing=true; startRecord(); };
  const up=()=>{ if(pressing){ pressing=false; stopRecord(); } };
  mic.addEventListener('mousedown', down);
  mic.addEventListener('touchstart', down, {passive:false});
  window.addEventListener('mouseup', up);
  mic.addEventListener('touchend', e=>{ e.preventDefault(); up(); }, {passive:false});
  mic.addEventListener('touchcancel', up);
})();

/* ===================== 渲染 ===================== */
function renderAll(){ updateMobileView(); renderContacts(); renderChat(); renderIdentity(); }
function renderIdentity(){
  document.getElementById('myName').textContent = store.identity.name;
  document.getElementById('myId').textContent = store.identity.id;
}
function renderContacts(){
  const list=document.getElementById('contactList'); list.innerHTML='';
  if(store.contacts.length===0){ list.innerHTML='<div style="padding:16px;color:var(--mut);font-size:12px;text-align:center">暂无联系人<br>点「新建连接」开始</div>'; return; }
  // 按最后联系排序
  const sorted=[...store.contacts].sort((a,b)=>(b.lastSeen||0)-(a.lastSeen||0));
  for(const c of sorted){
    const div=document.createElement('div');
    div.className='contact'+(c.id===currentId?' active':'');
    const last = c.lastSeen? fmtTime(c.lastSeen):'';
    const u = store.unread[c.id]||0;
    div.innerHTML=`<span class="dot${connections.has(c.id)?' on':''}"></span>
      <div class="c-main"><div class="c-name">${contactDisplayHtml(c)}</div>
      <div class="c-ip">${c.ip?escapeHtml(c.ip):'未知 IP'}</div></div>
      <div class="c-time">${u?`<span class="badge">${u>99?'99+':u}</span>`:last}</div>`;
    div.onclick=()=>selectContact(c.id);
    list.appendChild(div);
  }
}
function renderChat(){ renderTopbar(); renderMessages(); }
function renderTopbar(){
  const btn=document.getElementById('btnDetail');
  const rc=document.getElementById('btnReconnect');
  const ta=document.getElementById('inputMsg');
  const ba=document.getElementById('btnAttach');
  const bm=document.getElementById('btnMic');
  if(!currentId){ document.getElementById('topTitle').textContent='未选择联系人'; document.getElementById('topSub').textContent=''; document.getElementById('topStatus').textContent=''; document.getElementById('topStatus').className='status'; btn.style.display='none'; rc.style.display='none'; ta.disabled=true; if(ba) ba.disabled=true; if(bm) bm.disabled=true; closeAttachMenu(); document.getElementById('messages').innerHTML=emptyHtml(); return; }
  const c=getContact(currentId); if(!c) return;
  document.getElementById('topTitle').textContent=contactDisplayText(c);
  document.getElementById('topSub').textContent=c.ip||'未知 IP';
  const st=document.getElementById('topStatus');
  const connected=connections.has(currentId);
  if(connected){ st.textContent='● 已连接'; st.className='status connected'; ta.disabled=false; if(ba) ba.disabled=false; if(bm) bm.disabled=false; }
  else{ st.textContent='● 未连接'; st.className='status'; ta.disabled=false; if(ba) ba.disabled=false; if(bm) bm.disabled=false; closeAttachMenu(); } // textarea 始终可用（离线可发送 pending 消息）；附件/话筒按钮保持可点击以触发离线提示（toggleAttachMenu/startRecord 拦截）
  btn.style.display='';
  rc.style.display= connected? 'none':'inline-block'; // 仅未连接时显示重连按钮
  if(!connected && !hasMessages(currentId)) document.getElementById('messages').innerHTML=notConnHtml();
}
function renderMessages(){
  const box=document.getElementById('messages');
  if(!currentId){ box.innerHTML=emptyHtml(); return; }
  if(!connections.has(currentId) && !hasMessages(currentId)){ box.innerHTML=notConnHtml(); return; }
  const arr=store.messages[currentId]||[];
  box.innerHTML='';
  const c = getContact(currentId);
  const lastRead = c && c.lastReadTs;
  let dividerShown = false;
  for(const m of arr){
    // 在第一个新消息（对方发来、时间晚于 lastReadTs）前插入分界线
    if(!dividerShown && lastRead && m.dir==='in' && !m.pending && m.ts > lastRead){
      const div = document.createElement('div');
      div.className = 'msg-divider';
      div.textContent = '── 以下为新消息 ──';
      box.appendChild(div);
      dividerShown = true;
    }
    const el=document.createElement('div');
    if(m.dir==='sys'){ el.className='sys'; el.textContent=m.text; }
    else if(m.file){
      el.className='msg file '+(m.dir==='out'?'out':'in');
      el.id='file-'+m.file.fid;
      renderFileCardInto(el, {fid:m.file.fid, name:m.file.name, size:m.file.size, dir:m.dir, ts:m.ts});
    }
    else if(m.image){
      el.className='msg image '+(m.dir==='out'?'out':'in');
      el.id='img-'+m.image.iid;
      renderImageInto(el, {iid:m.image.iid, name:m.image.name, size:m.image.size, dir:m.dir, ts:m.ts});
    }
    else if(m.video){
      el.className='msg video '+(m.dir==='out'?'out':'in');
      el.id='vid-'+m.video.vid;
      renderVideoInto(el, {vid:m.video.vid, name:m.video.name, size:m.video.size, dir:m.dir, ts:m.ts});
    }
    else if(m.audio){
      el.className='msg audio '+(m.dir==='out'?'out':'in');
      el.id='aud-'+m.audio.aid;
      renderAudioInto(el, {aid:m.audio.aid, name:m.audio.name, size:m.audio.size, dir:m.dir, ts:m.ts});
    }
    else{
      el.className='msg '+(m.dir==='out'?'out':'in');
      el.dataset.ts=m.ts;
      if(typeof m.seq==='number') el.dataset.seq = m.seq;
      const statusTag = m.pending
        ? '<span class="read-tag pending">⏳ 未发送</span>'
        : (m.dir==='out'?`<span class="read-tag" data-ts="${m.ts}" data-seq="${typeof m.seq==='number'?m.seq:''}"></span>`:'');
      el.innerHTML=escapeHtml(m.text)+`<div class="t">${fmtTime(m.ts)}${statusTag}</div>`;
    }
    box.appendChild(el);
  }
  box.scrollTop=box.scrollHeight;
  // 刷新已读回执标记
  if(currentId) refreshMessageReadStatus(currentId);
}
function hasMessages(id){ return !!(store.messages[id]&&store.messages[id].length); }
function emptyHtml(){
  return `<div id="empty"><h2>🌍 P2PChat</h2><p>基于 WebRTC 的 IPv6/IPv4 端到端加密 P2P 聊天<br>无需服务器，单文件打开即用</p>
  <p style="margin-top:14px">点左侧「新建连接」或「接受连接」开始</p></div>`;
}
function notConnHtml(){
  return `<div class="notconn" style="margin:auto"><b>未与该联系人建立连接</b><br><br>
    因 WebRTC 会话信息每次临时生成，无法凭 IP 自动重连。<br>请重新交换一次连接码：
    <div style="margin-top:10px"><button onclick="startInvite()">我发起连接</button><button class="ghost" onclick="startAccept()">我接受连接</button></div></div>`;
}

/* ===================== 对话框 ===================== */
function showConnectDialog(steps){
  const body=document.getElementById('dlgBody'); body.innerHTML='';
  for(const s of steps){
    const sec=document.createElement('div'); sec.style.marginBottom='18px';
    sec.innerHTML=`<div class="step">${s.step}</div>${s.body}`;
    body.appendChild(sec);
  }
  document.getElementById('dlgConnect').classList.add('show');
}
function closeDialog(id){ document.getElementById(id).classList.remove('show'); }
/* 取消连接向导：关闭对话框并清理握手中的 PC，使进行中的 startInvite/acceptOffer 检测到中断后中止 */
function cancelConnect(){
  closeDialog('dlgConnect');
  cleanupPending();
  pendingPeerIps = null;
}

/* 详情 */
function openDetail(){
  if(!currentId) return;
  const c=getContact(currentId);
  document.getElementById('dName').value= c.nameSet ? (c.name||'') : '';
  document.getElementById('dPeer').textContent= c.peerName || '（连接后同步）';
  document.getElementById('dIp').value=c.ip||'';
  document.getElementById('dNote').value=c.note||'';
  document.getElementById('dSeen').textContent=c.lastSeen? new Date(c.lastSeen).toLocaleString():'—';
  renderDetailIpInfo(c);
  document.getElementById('dlgDetail').classList.add('show');
}
function renderDetailIpInfo(c){
  const el=document.getElementById('dIpInfo'); if(!el) return;
  if(connections.has(c.id)){
    const mode=ipModeLabel(c.ipType);
    el.innerHTML = `当前对端地址：<b style="font-family:Consolas,monospace">${escapeHtml(c.ip||'未知')}</b>${mode?` <span class="pill">${mode}</span>`:''}`;
  }else{
    el.innerHTML = `当前对端地址：<span style="color:var(--mut)">未连接（上次：${escapeHtml(c.ip||'—')}${c.ipType?(' · '+ipModeLabel(c.ipType)):''}）</span>`;
  }
}
function saveDetail(){
  const c=getContact(currentId); if(!c) return;
  const nm=document.getElementById('dName').value.trim();
  c.name=nm;
  c.nameSet=!!nm; // 有备注才标记，空则回退显示对方用户名
  c.ip=document.getElementById('dIp').value.trim();
  c.note=document.getElementById('dNote').value;
  saveStore(); renderAll(); closeDialog('dlgDetail'); toast("已保存");
}
function deleteContact(){
  if(!currentId) return;
  if(!confirm("确定删除该联系人及其聊天记录？")) return;
  const conn = connections.get(currentId);
  if(conn){
    if(conn.chat){ const info=channelMap.get(conn.chat); if(info) channelMap.delete(conn.chat); }
    if(conn.file){ const info=channelMap.get(conn.file); if(info) channelMap.delete(conn.file); }
    try{ conn.pc.close(); }catch(e){}
    for(const [seq,p] of conn.pending) clearTimeout(p.timer);
    conn.pending.clear();
    stopHeartbeat(conn);
    connections.delete(currentId);
  }
  // 关闭可能残留在 revivable 中的 PC，防止 ICE 连接泄漏
  const rv = revivable.get(currentId);
  if(rv){ try{ rv.close(); }catch(e){} }
  revivable.delete(currentId); cancelAutoRevive(currentId); autoReviveRetries.delete(currentId); peerBye.delete(currentId);
  stopContactAudioPlayers(currentId); // 释放语音播放器内存
  revokeContactUrls(currentId);       // 释放文件/图片/视频/语音 objectURL 内存
  store.contacts=store.contacts.filter(c=>c.id!==currentId);
  delete store.messages[currentId];
  currentId=null; saveStore(); renderAll(); closeDialog('dlgDetail'); toast("已删除");
}
function clearHistory(){
  if(!currentId) return;
  if(!confirm("清空与该联系人的聊天记录？")) return;
  stopContactAudioPlayers(currentId); // 释放语音播放器内存
  revokeContactUrls(currentId);       // 释放文件/图片/视频/语音 objectURL 内存
  store.messages[currentId]=[]; saveStore(); renderMessages(); closeDialog('dlgDetail'); toast("已清空");
}

/* 设置 */
function openSettings(){
  document.getElementById('setName').value=store.identity.name;
  document.getElementById('dlgSettings').classList.add('show');
}
function saveSettings(){
  const newName=document.getElementById('setName').value.trim();
  const changed = !!newName && newName!==store.identity.name;
  if(changed) store.identity.name=newName;
  saveStore(); renderIdentity(); closeDialog('dlgSettings'); toast("已保存");
  if(changed){ // 向所有已连接联系人同步新名字（对端收到 hello 即更新）
    const hello=JSON.stringify({type:"hello", identity: store.identity});
    connections.forEach(conn=>{ if(conn.chat) try{ conn.chat.send(hello); }catch(e){} });
  }
}

/* ===================== 账号引导 / 退出 ===================== */
let onboarding=false; // 引导态：导入成功后需关闭引导弹窗
function boot(){
  renderAll();
  refreshMyIp();
  syncMobileHistory(); // 注入根历史项，拦截列表页返回键
  if(!localStorage.getItem(STORE_KEY)){ showOnboard(); } // 首次启动无数据 → 引导
}
function showOnboard(){ document.getElementById('dlgOnboard').classList.add('show'); }
function onboardNew(){
  saveStore(); // 持久化新身份
  closeDialog('dlgOnboard');
  document.getElementById('dlgOnboardTips').classList.add('show'); // 操作提示（可跳过）
}
function onboardImport(){ onboarding=true; importJSON(); }
function logoutAccount(){
  closeDialog('dlgSettings');
  document.getElementById('dlgLogout').classList.add('show');
}
async function doLogout(backup){
  closeDialog('dlgLogout');
  if(backup) await exportJSON(); // 退出前导出一份备份（await 确保导出完成再清数据）
  localStorage.removeItem(STORE_KEY);
  channelMap.forEach(i=>{try{i.pc.close();}catch(e){}});
  connections.forEach(conn=>{ for(const [seq,p] of conn.pending) clearTimeout(p.timer); conn.pending.clear(); stopHeartbeat(conn); });
  if(recReleaseTimer){ clearTimeout(recReleaseTimer); recReleaseTimer=null; }
  if(recStream){ try{ recStream.getTracks().forEach(t=>t.stop()); }catch(e){} recStream=null; }
  connections.clear(); channelMap.clear(); revivable.clear(); peerBye.clear();
  autoReviveTimers.forEach(t=>clearTimeout(t)); autoReviveTimers.clear(); autoReviveRetries.clear();
  stopAllAudioPlayers(); revokeAllUrls(); // 释放所有语音播放器与传输 objectURL 内存
  currentId=null; clearConnectWatchdog();
  store=defaultStore(); // 内存占位，不保存 → 保持 localStorage 为空，下次启动仍引导
  renderAll();
  showOnboard();
  toast(backup?"已导出备份并退出账号":"已退出账号");
}

/* ===================== 导入导出 ===================== */
async function exportJSON(){
  const blob=new Blob([JSON.stringify(store,null,2)],{type:'application/json'});
  const d=new Date(); const p=n=>String(n).padStart(2,'0');
  const filename=`p2pchat-${store.identity.name}-${d.getFullYear()}${p(d.getMonth()+1)}${p(d.getDate())}.json`
    .replace(/[\\/:*?\"<>|]/g,'_'); // 过滤 Windows 文件名非法字符
  // 移动端优先 Web Share API：弹出系统分享/保存菜单，体验最可靠
  const file=new File([blob],filename,{type:'application/json'});
  try{
    if(navigator.canShare && navigator.canShare({files:[file]})){
      await navigator.share({files:[file], title:`P2PChat 备份 - ${store.identity.name}`, text:filename});
      toast("已导出"); return;
    }
  }catch(e){ if(e && e.name==='AbortError') return; /* 用户取消则结束，否则回退到下载 */ }
  // 回退：a[download]，需挂到 DOM 才能在部分移动浏览器触发
  const url=URL.createObjectURL(blob);
  const a=document.createElement('a');
  a.href=url; a.download=filename; a.rel='noopener';
  document.body.appendChild(a); a.click(); a.remove();
  setTimeout(()=>URL.revokeObjectURL(url), 2000);
  toast("已导出；若未弹出下载，请用系统浏览器打开本页再导出");
}
function importJSON(){ document.getElementById('fileInput').click(); }
document.getElementById('fileInput').addEventListener('change', e=>{
  try{
    const f=e.target.files[0]; if(!f) return;
    const r=new FileReader();
    r.onload=()=>{
      try{
        const d=JSON.parse(r.result);
        if(!d.identity || !Array.isArray(d.contacts)) throw new Error("格式不符");
        if(!confirm("导入将覆盖当前数据，是否继续？")){ onboarding=false; return; }
        store={...defaultStore(), ...d};
        if(!store.messages) store.messages={};
        if(!store.settings) store.settings={};
        if(!store.unread) store.unread={};
        store.version=4; // 仅直连，忽略历史 STUN 配置
        connections.forEach(conn=>{ for(const [seq,p] of conn.pending) clearTimeout(p.timer); conn.pending.clear(); stopHeartbeat(conn); });
        saveStore(); connections.clear(); currentId=null; renderAll(); toast("导入成功");
        if(onboarding){ onboarding=false; closeDialog('dlgOnboard'); }
      }catch(err){ toast("导入失败: "+err.message); }
    };
    r.onerror=()=>{ toast("文件读取失败"); };
    r.readAsText(f); e.target.value='';
  }catch(err){ console.error('import input:',err); toast('操作失败'); }
});

/* ===================== 工具 ===================== */
function escapeHtml(s){ return String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c])); }
function copyText(t){
  if(!t) return;
  if(navigator.clipboard && navigator.clipboard.writeText){
    navigator.clipboard.writeText(t).then(()=>toast("已复制")).catch(()=>fallbackCopy(t));
  } else fallbackCopy(t);
}
function fallbackCopy(t){
  const ta=document.createElement('textarea'); ta.value=t; ta.style.position='fixed'; ta.style.opacity='0';
  document.body.appendChild(ta); ta.select();
  try{ document.execCommand('copy'); toast("已复制"); }catch(e){ toast("复制失败，请手动选择复制"); }
  document.body.removeChild(ta);
}
let toastTimer=null;
function toast(msg, ms){
  const el=document.getElementById('toast'); el.textContent=msg; el.classList.add('show');
  clearTimeout(toastTimer); toastTimer=setTimeout(()=>el.classList.remove('show'), ms||2200);
}

let exitAllowed=false; // 用户已在退出确认中选择"退出"，放行浏览器返回
// 移动端历史栈同步：确保栈顶有与当前视图匹配的拦截条目（root/chat）。
// PC 下 boot/selectContact 不 pushState，缩窗到手机后补注入，让返回键与 backBtn 行为一致。
function syncMobileHistory(){
  if(!isMobile()) return;
  const want = currentId ? 'chat' : 'root';
  if(!(history.state && history.state.p2pchat===want)){
    try{ history.pushState({p2pchat:want}, ''); }catch(e){}
  }
}
if(window.matchMedia){
  const mq = window.matchMedia('(max-width:680px)');
  const onMq = ()=>syncMobileHistory();
  if(mq.addEventListener) mq.addEventListener('change', onMq);
  else if(mq.addListener) mq.addListener(onMq); // 旧版 Safari 兼容
}
window.addEventListener('popstate', ()=>{
  if(currentId){ goBack(); return; } // 聊天视图 → 回到列表
  if(isMobile() && !exitAllowed){ showExitConfirm(); return; } // 列表视图 → 拦截退出，弹确认
});
/* 后台/息屏恢复探测：iOS 墓碑机制与安卓息屏冻结页面时，ICE keepalive 与心跳定时器随 JS 暂停。
   恢复前台后底层网络通常未变——立即对每个已连接联系人补发 ping 激活 ICE、探测存活；
   对断开待恢复（revivable）的连接立即触发 autoRevive（墓碑恢复后 ICE 可能仍存活，可免交换码恢复）。 */
document.addEventListener('visibilitychange', ()=>{
  if(document.visibilityState !== 'visible') return;
  for(const cId of connections.keys()) sendPing(cId);
  for(const cId of revivable.keys()){
    if(!peerBye.has(cId) && !autoReviveTimers.has(cId) && !connections.has(cId)){
      autoReviveRetries.delete(cId); // 恢复前台视为新的恢复周期，重置重试计数
      scheduleAutoRevive(cId, true);
    }
  }
});
function showExitConfirm(){ document.getElementById('dlgExitConfirm').classList.add('show'); }
function confirmExit(yes){
  closeDialog('dlgExitConfirm');
  if(yes){ exitAllowed=true; try{ history.back(); }catch(e){} } // 放行，离开页面
  else { try{ history.pushState({p2pchat:'root'},''); }catch(e){} } // 取消：重新拦截下次返回
}
window.addEventListener('beforeunload', ()=>{
  channelMap.forEach(i=>{try{i.pc.close();}catch(e){}});
  if(recReleaseTimer) clearTimeout(recReleaseTimer);
  if(recStream){ try{ recStream.getTracks().forEach(t=>t.stop()); }catch(e){} recStream=null; }
});

/* 启动 */
boot();