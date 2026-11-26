import{mkdirSync,readdirSync,readFileSync,writeFileSync}from'node:fs';
import{join}from'node:path';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
const X=[0,0,-1,1],Y=[-1,1,0,0],C=['u','d','l','r'];
// Parse XSB text into a board.
const P=t=>{const r=t.split('\n').filter(x=>x.length),h=r.length,w=Math.max(...r.map(x=>x.length)),a=new Uint8Array(w*h).fill(1),g=[],b=[];let p=-1;
r.forEach((s,y)=>{for(let x=0;x<s.length;x++){const i=y*w+x,q=s[x];if(q==='#')continue;a[i]=0;
if(q==='.'||q==='*'||q==='+')g.push(i);if(q==='$'||q==='*')b.push(i);if(q==='@'||q==='+')p=i;}});
return{w,h,wall:a,goals:g,boxes:b,player:p}};
// Squares a box can be pulled back to from some goal.
const V=(w,a,g)=>{const v=new Uint8Array(a.length),q=[...g];for(const x of g)v[x]=1;
for(let k=0;k<q.length;k++)for(let d=0;d<4;d++){const s=Y[d]*w+X[d],y=q[k]-s,z=y-s;
if(y>=0&&y<a.length&&z>=0&&z<a.length&&!a[y]&&!a[z]&&!v[y]){v[y]=1;q.push(y);}}return v};
// Flood from a square around walls and boxes; marks seen, returns the lowest square.
const F=(w,a,o,f,s,t)=>{let l=f;const q=[f];s[f]=t;
for(let n=0;n<q.length;n++){const p=q[n];if(p<l)l=p;
for(let k=0;k<4;k++){const u=p+(k?k===1?w:k===2?-1:1:-w);
if(u>=0&&u<a.length&&!a[u]&&!o[u]&&s[u]!==t){s[u]=t;q.push(u);}}}return l};
// True when the box just pushed to t is stuck in a 2x2 block of walls/boxes off-goal.
const Z=(w,a,o,g,t)=>{for(const x of[t,t-1,t-w,t-w-1]){if(x<0||x%w>=w-1||x+w+1>=a.length)continue;
const b=x+1,c=x+w,d=c+1;
if((a[x]||o[x])&&(a[b]||o[b])&&(a[c]||o[c])&&(a[d]||o[d])&&((o[x]&&!g[x])||(o[b]&&!g[b])||(o[c]&&!g[c])||(o[d]&&!g[d])))return 1}return 0};
// Shortest player walk (lowercase LURD) from f to t around walls and boxes.
const W=(w,a,o,f,t)=>{if(f===t)return'';const v=new Int32Array(a.length).fill(-1),h=new Array(a.length),q=[f];v[f]=f;
for(let k=0;k<q.length;k++){const p=q[k];if(p===t)break;
for(let j=0;j<4;j++){const n=p+Y[j]*w+X[j];
if(n<0||n>=a.length||a[n]||o[n]||v[n]!==-1)continue;v[n]=p;h[n]=C[j];q.push(n);}}
if(v[t]===-1)throw 0;let s='';for(let p=t;p!==f;p=v[p])s=h[p]+s;return s};
// Binary heap ordered by [f, h, insertion order].
const cmp=(a,b)=>a[0]-b[0]||a[1]-b[1]||a[2]-b[2];
const HP=(h,v)=>{h.push(v);let i=h.length-1;
while(i>0){const p=i-1>>1;if(cmp(h[p],h[i])<=0)break;const t=h[p];h[p]=h[i];h[i]=t;i=p}};
const HO=h=>{const t=h[0],l=h.pop();if(h.length){h[0]=l;let i=0;
for(;;){const a=2*i+1,b=a+1;let m=i;
if(a<h.length&&cmp(h[a],h[m])<0)m=a;if(b<h.length&&cmp(h[b],h[m])<0)m=b;
if(m===i)break;const x=h[m];h[m]=h[i];h[i]=x;i=m}}return t};
// Push-optimal A* over pushes for one board. Move string, or null on exhaustion.
const S=(L,cap)=>{
const{w,wall,goals,boxes,player}=L,n=boxes.length,size=wall.length;
const goal=new Uint8Array(size);for(const g of goals)goal[g]=1;
const lv=V(w,wall,goals);if(boxes.some(b=>!lv[b]))return null;
const dist=goals.map(g=>{const d=new Int32Array(size).fill(-1);d[g]=0;const q=[g];
for(let k=0;k<q.length;k++){const p=q[k];
for(let j=0;j<4;j++){const u=p+Y[j]*w+X[j];
if(u>=0&&u<size&&!wall[u]&&d[u]<0){d[u]=d[p]+1;q.push(u);}}}return d});
let heur;
if(n>4)heur=bs=>{let s=0;for(const b of bs){let m=1e9;
for(const d of dist)if(d[b]>=0&&d[b]<m)m=d[b];s+=m}return s};
else{const pm=[],mk=(a,r)=>{if(r===n){pm.push(a.slice());return}
for(let i=0;i<n;i++)if(!a.includes(i)){a.push(i);mk(a,r+1);a.pop()}};mk([],0);
heur=bs=>{let best=1e9;for(const p of pm){let s=0;
for(let i=0;i<n;i++){const d=dist[p[i]][bs[i]];if(d<0){s=1e9;break}s+=d}
if(s<best)best=s}return best}}
const occ=new Uint8Array(size),seen=new Int32Array(size),mark=new Int32Array(size);
let stamp=0;
const BX=[boxes.slice().sort((a,b)=>a-b)],PL=[player],PA=[-1],PF=[-1],PT=[-1],GS=[0];
const idx=new Map(),key=(bs,lo)=>bs.join(',')+':'+lo;
for(const b of BX[0])occ[b]=1;
idx.set(key(BX[0],F(w,wall,occ,player,seen,++stamp)),0);
for(const b of BX[0])occ[b]=0;
const hp=[];let cnt=0;const h0=heur(BX[0]);HP(hp,[h0,h0,cnt++,0,0]);
let found=-1;
while(hp.length){
const e=HO(hp),s=e[3];if(e[4]!==GS[s])continue;
const bs=BX[s];if(bs.every(b=>goal[b])){found=s;break}
for(const b of bs)occ[b]=1;
F(w,wall,occ,PL[s],seen,++stamp);const here=stamp;
for(let bi=0;bi<n;bi++){const b=bs[bi];
for(let j=0;j<4;j++){const st=Y[j]*w+X[j],stand=b-st,t=b+st;
if(stand<0||stand>=size||t<0||t>=size)continue;
if(seen[stand]!==here||wall[t]||occ[t]||!lv[t])continue;
occ[b]=0;occ[t]=1;const fr=Z(w,wall,occ,goal,t);
let nb=null,k='';
if(!fr){nb=bs.slice();nb[bi]=t;nb.sort((x,y)=>x-y);k=key(nb,F(w,wall,occ,b,mark,++stamp))}
occ[t]=0;occ[b]=1;if(fr)continue;
const g=GS[s]+1,old=idx.get(k);
if(old!==undefined){if(GS[old]<=g)continue;
GS[old]=g;PA[old]=s;PF[old]=b;PT[old]=t;PL[old]=b;
const h=heur(nb);HP(hp,[g+h,h,cnt++,old,g]);continue}
if(BX.length>=cap)return null;
idx.set(k,BX.length);BX.push(nb);PL.push(b);PA.push(s);PF.push(b);PT.push(t);GS.push(g);
const h=heur(nb);HP(hp,[g+h,h,cnt++,BX.length-1,g])}}
for(const b of bs)occ[b]=0}
if(found<0)return null;
const path=[];for(let s=found;s>0;s=PA[s])path.push(s);path.reverse();
let moves='',pl=player,cur=BX[0];
for(const s of path){const nb=BX[s],from=PF[s],to=PT[s],d=to-from;
const j=d===-w?0:d===w?1:d===-1?2:3;
for(const b of cur)occ[b]=1;moves+=W(w,wall,occ,pl,from-d);
for(const b of cur)occ[b]=0;moves+=C[j];pl=from;cur=nb}
return moves};
// Split a level into rooms: cut the hallway row's dead squares, flood the rest.
const R=L=>{
const{w,wall,goals,boxes,player}=L,lv=V(w,wall,goals);
const row=Math.floor(player/w),cut=new Uint8Array(wall.length);
for(let i=row*w;i<(row+1)*w;i++)if(!wall[i]&&!lv[i])cut[i]=1;
if(boxes.some(b=>cut[b]))return null;
const part=new Int32Array(wall.length).fill(-1),rooms=[];
for(let s=0;s<wall.length;s++){if(wall[s]||cut[s]||part[s]>=0)continue;
const sq=[s];part[s]=rooms.length;
for(let k=0;k<sq.length;k++){const p=sq[k];
for(let j=0;j<4;j++){const q=p+Y[j]*w+X[j];
if(q>=0&&q<wall.length&&!wall[q]&&!cut[q]&&part[q]<0){part[q]=rooms.length;sq.push(q)}}}
rooms.push({boxes:[],goals:[]})}
for(const b of boxes)rooms[part[b]].boxes.push(b);
for(const g of goals){if(part[g]<0)return null;rooms[part[g]].goals.push(g)}
if(rooms.some(r=>r.boxes.length!==r.goals.length))return null;
return rooms.filter(r=>r.boxes.length>0)};
const E=(w,from,moves)=>{let p=from;
for(const c of moves)p+=c==='u'?-w:c==='d'?w:c==='l'?-1:1;return p};
// Solve room by room (other rooms' boxes, or goals once done, act as walls); else the whole board.
const solveLevel=L=>{
const rooms=R(L);
if(rooms){let moves='',pl=L.player;
for(const r of rooms){const wl=L.wall.slice();
for(const o of rooms)if(o!==r)for(const b of(o.done?o.goals:o.boxes))wl[b]=1;
const m=S({w:L.w,wall:wl,goals:r.goals,boxes:r.boxes,player:pl},300000);
if(m===null)return S(L,1000000)??'';
moves+=m;pl=E(L.w,pl,m);r.done=true}
return moves}
return S(L,1000000)??''};
for(const id of readdirSync(I).sort()){
let m='';
try{m=solveLevel(P(readFileSync(join(I,id,'level.txt'),'utf8')))}catch(e){m=''}
mkdirSync(join(O,id),{recursive:true});
writeFileSync(join(O,id,'solution.txt'),m+'\n')}
