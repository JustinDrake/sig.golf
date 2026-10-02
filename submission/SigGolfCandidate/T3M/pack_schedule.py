"""Static assembler transform; never executes a candidate or benchmark.
Input is the committed packed-header integration image. Preserve other labels;
compact each FTS ladder in its allocated slot and relocate direct branches.
"""
from pathlib import Path
import re, subprocess, hashlib
BASE = '962fcf4'
p = Path('submission/SigGolfCandidate/T3M/Images/Verify.lean')
s = subprocess.check_output(['git','show',BASE+':'+str(p)],text=True)
a = [int(v,16) for m in re.finditer(r'def verifyCode_\d+ : List \(BitVec 32\) := \[(.*?)\]',s,re.S) for v in re.findall(r'0x[0-9a-f]+',m[1])]
def sx(v,n): return v-(1<<n) if v>>(n-1) else v
def jal(pc,target,rd=0):
 d=4*(target-pc);assert -(1<<20)<=d<(1<<20);u=d&((1<<21)-1)
 return (u>>20)<<31|((u>>1)&1023)<<21|((u>>11)&1)<<20|((u>>12)&255)<<12|rd<<7|0x6f
def branch(pc,target,w):
 d=4*(target-pc);assert -(1<<12)<=d<(1<<12);u=d&8191
 return (w&0x01fff07f)|(u>>12)<<31|((u>>5)&63)<<25|((u>>1)&15)<<8|((u>>11)&1)<<7
intervals=[(4841,4856),(4865,4975),(4975,5085),(5085,5186),(5186,5287),(5287,5385),(5385,5483)]
def removed(w):
 return w&127==0x23 and (w>>12&7)==2 and (w>>15&31)==10 and (w>>20&31)==22 and ((w>>25<<5)|(w>>7&31))==20
mapping={i:i for i in range(len(a))};dead=set()
for lo,hi in intervals:
 kept=[i for i in range(lo,hi) if not removed(a[i])]
 for dest,src in enumerate(kept,lo):mapping[src]=dest
 dead.update(set(range(lo,hi))-set(kept))
out=a.copy()
for lo,hi in intervals:out[lo:hi]=[0x13]*(hi-lo)
for i,w in enumerate(a):
 if i in dead:continue
 pc=mapping[i];op=w&127
 if op==0x6f:
  d=sx(((w>>31)<<20)|((w>>21&1023)<<1)|((w>>20&1)<<11)|((w>>12&255)<<12),21)
  assert d%4==0;target=i+d//4;assert target not in dead
  if pc!=i or mapping.get(target,target)!=target:w=jal(pc,mapping.get(target,target),w>>7&31)
 elif op==0x63:
  d=sx(((w>>31)<<12)|((w>>25&63)<<5)|((w>>8&15)<<1)|((w>>7&1)<<11),13)
  assert d%4==0;target=i+d//4;assert target not in dead
  if pc!=i or mapping.get(target,target)!=target:w=branch(pc,mapping.get(target,target),w)
 out[pc]=w
# The old setup address remains an entry trampoline; the extra code fits chunk 819.
stub=len(out);body=a[359:377]+[0x020b1193,0x003d8db3] # slli x3,x22,32; add x27,x27,x3
out[359]=jal(359,stub)
out+=body+[jal(stub+len(body),377)]
assert len(out)<=256*820
for lo,hi in intervals:print(f'{lo}:{hi}: removed {sum(i in dead for i in range(lo,hi))} static stores')
def patch(m):
 start=int(m[1])*256;vals=out[start:min(start+256,len(out))]
 return m[0][:m[0].index('[')+1]+'\n'+',\n'.join('  '+', '.join(f'0x{v:08x}' for v in vals[j:j+8]) for j in range(0,len(vals),8))+']'
s=re.sub(r'def verifyCode_(\d+) : List \(BitVec 32\) := \[(.*?)\]',patch,s,flags=re.S)
digest=hashlib.sha256(b''.join(v.to_bytes(4,'little') for v in out)).hexdigest()
lines=s.splitlines();lines[:2]=[f'-- Precomputed packed node-header candidate: {len(out)} instruction words.',f'-- Static little-endian instruction-byte SHA-256: {digest}. Official validation required.']
p.write_text('\n'.join(lines)+'\n')
print(f'Setup trampoline {stub}, total words {len(out)}; no execution performed.')
