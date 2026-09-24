"""Reproduce manuscript arithmetic and four vector figures; no random sampling.

From repository root:
  .venv/Scripts/python.exe key_results/RAFs/How_to_Design_an_Assay_arxiv/reproduce.py
All calculations are synthetic source examples, not measured performance.
"""
from pathlib import Path
from fractions import Fraction as F
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch

HERE = Path(__file__).resolve().parent
FIG = HERE / 'figures'
FIG.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
    'axes.spines.top':False,'axes.spines.right':False,
    'pdf.fonttype':42,'ps.fonttype':42,'axes.titleweight':'bold',
    'axes.labelcolor':'#243444','text.color':'#243444','axes.edgecolor':'#667788',
    'savefig.bbox':'tight'})
blue, orange, gray = '#27689D', '#CA7135', '#8B98A5'

def save(fig, name):
    fig.savefig(FIG / (name+'.pdf'))
    fig.savefig(FIG / (name+'.png'), dpi=170)
    plt.close(fig)

def lower(q1,q2,B,e,s,J,H):
    return max(0,q1-B,q1+q2-B-H,e*q1+q2-e*B-(s-e)*J-H,s*q1+q2-s*B-H)

def occ(u,C=1.,K=1.):
    return 2*C/(u+C+K+np.sqrt((u-C)**2+2*K*(u+C)+K*K))

def hook(u):
    return u*occ(u)**2

# Exact arithmetic checks from the statements, independently recomputed.
assert 42*F(9,14)+40*F(11,8)==82
p_bulk=(1-F(9,14))/(F(11,8)-F(9,14))
p_low=(F(68,100)-F(2,100))/(1-F(2,100))
p_high=F(72,100)/F(9,10)
assert (p_bulk,p_low,p_high)==(F(20,41),F(33,49),F(4,5))
assert p_low-F(2,3)==F(1,147)
a=F(9,20); H=(1-a)**6; m=9
z=F(m,m+1)/(1-H)
gate=z**m*(1-(1-H)*z)
assert 0<z<1 and gate<F(1,20)
availability=F(24,25)**9
q1=F(29,5); q2=F(19,5); B=F(10); J=F(2); recovery=F(1,5)
washed=lower(q1,q2,B,F(1,20),F(9,10),J,recovery)
unwashed=lower(q1,F(11,2),B,F(9,10),F(9,10),J,recovery)
assert (washed,unwashed)==(F(169,100),F(38,25))
assert lower(q1,q2,B,F(1,20),F(9,10),F(179,85),recovery)==F(8,5)
# A matched feasible account: collect 6 from initial 10, leave P=R=2,
# then retain pools, add 0.2 recovery material and 2.1 fresh material.
true_w=F(1,20)*2+F(9,10)*2+F(1,5)+F(21,10)
true_u=F(9,10)*4+F(1,5)+F(21,10)
assert abs(true_w-4)<=F(1,5) and abs(true_u-F(57,10))<=F(1,5)
fi=lambda k: 1-F(k+5,4*2**k)
fw=lambda k: 1-F(k+1,2**(k+1))
assert fi(5)<F(19,20)<=fi(6) and fw(6)<F(19,20)<=fw(7)
assert (fi(6),fw(6),fi(7),fw(7))==(F(245,256),F(121,128),F(125,128),F(31,32))
suppression=F(400869,8492000)
residual=F(56426461,150750000)-F(126420993,362500000)-F(1,50)
assert suppression<F(473,10000) and residual==F(1214759671,218587500000)
assert residual>F(55,10000)
# Test the equivalence of the max and remaining-stock formula on a small exact grid.
# This is arithmetic QA, not a proof of the continuum theorem.
for qfirst in map(F,[0,2,6,12]):
    for qsecond in map(F,[0,1,4,9]):
        for reserve in map(F,[0,2,20]):
            for e,s in [(F(0),F(0)),(F(1,20),F(9,10)),(F(1),F(1))]:
                A=max(0,qfirst-B); x=max(0,B-qfirst)
                K=e*x+(s-e)*min(reserve,x)
                assert lower(qfirst,qsecond,B,e,s,reserve,recovery)==A+max(0,qsecond-recovery-K)
u=np.logspace(-3,3,300)
p=occ(u)
assert np.max(np.abs(u*p+p/(1-p)-1))<1e-10
assert abs(hook(.08)-hook(50))<1e-14
results={'evidence':'exact rational arithmetic except labeled floating illustrations',
    'bulk_lower':str(p_bulk),'readout_lower':str(p_low),'readout_upper':str(p_high),
    'decision_margin':str(p_low-F(2,3)), 'specimen_H':str(H),
    'gate_bound_exact':str(gate),'gate_bound_decimal':float(gate),
    'blank_availability_exact':str(availability),'blank_availability_decimal':float(availability),
    'washed':str(washed),'unwashed':str(unwashed),
    'matched_true_collections':[str(true_w),str(true_u)],
    'count_cdfs':{str(k):{'independent':str(fi(k)),'shared':str(fw(k))} for k in [5,6,7]},
    'loading_floor_float':float(np.exp(-4)*.99),
    'suppression_exact':str(suppression),'signal_margin_exact':str(residual),
    'material_grid_cases':4*4*3*3,'checks_passed':True}
(HERE/'calculations.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')

fig,axs=plt.subplots(1,2,figsize=(10,3.4),gridspec_kw={'width_ratios':[1,1.15]},layout='constrained')
ax=axs[0]
ax.barh([1,0],[82,40],color=blue,height=.48,label='Reaches target')
ax.barh([1,0],[0,42],left=[82,40],color='#D6DEE6',height=.48,label='Does not reach target')
ax.set(yticks=[1,0],yticklabels=['Uniform\n82 at capacity 1','Heterogeneous\n42 low, 40 high'],xlim=(0,86),xlabel='Units (same mean capacity = 1)')
ax.text(41,1,'82',ha='center',va='center',color='white',weight='bold')
ax.text(20,0,'40',ha='center',va='center',color='white',weight='bold')
ax.text(61,0,'42',ha='center',va='center')
ax.set_title('A   Same pooled response',loc='left',fontsize=11)
ax.legend(loc='upper center',bbox_to_anchor=(.5,-.25),fontsize=8,frameon=False)
ax=axs[1]
ax.hlines([1,0],[float(p_bulk)*100,float(p_low)*100],[100,80],colors=[gray,blue],linewidth=9)
ax.scatter([float(p_bulk)*100,100,float(p_low)*100,80],[1,1,0,0],c=[gray,gray,blue,blue],s=35,zorder=3)
ax.axvline(100*2/3,color=orange,ls='--',lw=1.4)
ax.text(100*2/3+1,1.5,'Two-thirds',color=orange,fontsize=9)
ax.text(74,1.18,'48.78–100%',ha='center',fontsize=9)
ax.text(75,-.3,'67.35–80%',ha='center',fontsize=9)
ax.set(xlim=(40,103),ylim=(-.65,1.85),yticks=[1,0],yticklabels=['Pooled only','With readout'],xlabel='Compatible recovery fraction (%)')
ax.set_title('B   Information changes the bound',loc='left',fontsize=11)
save(fig,'enzyme')

fig,axs=plt.subplots(1,2,figsize=(10,3.5),layout='constrained')
ax=axs[0]; u=np.logspace(-2,3,700)
ax.semilogx(u,hook(u),color=blue,label='Neat',lw=2)
ax.semilogx(u,hook(u/10),color=orange,label='Tenfold diluted',lw=2)
ax.scatter([.08,50],hook(np.array([.08,50])),color=blue,zorder=3)
ax.scatter([.08,50],hook(np.array([.08,50])/10),color=orange,zorder=3)
ax.set(xlabel='Accessible concentration u (model units)',ylabel='Sandwich concentration B',ylim=(0,.19))
ax.set_title('A   Same neat signal, different dilution',loc='left',fontsize=11)
ax.legend(frameon=False,fontsize=9)
ax=axs[1];ax.axis('off')
for y,label in [(.8,'Native x = 0.1\nAvailability ρ = 1'),(.25,'Native x = 100\nAvailability ρ = 0.001')]:
    ax.text(.02,y,label,va='center',fontsize=11,bbox=dict(boxstyle='round,pad=.5',fc='#EDF3F8',ec='none'))
    ax.annotate('',xy=(.65,.52),xytext=(.48,y),arrowprops=dict(arrowstyle='->',color=gray,lw=1.8))
ax.text(.73,.52,'Accessible\nu = 0.1\n\nSame record',ha='center',va='center',fontsize=11)
ax.set_title('B   Dilution does not establish availability',loc='left',fontsize=11)
save(fig,'hook')

fig,axs=plt.subplots(1,2,figsize=(10,3.5),layout='constrained')
ax=axs[0]; x=np.arange(2)
ax.bar(x-.17,[4,5.7],.32,color=gray,label='Second-window reading')
ax.bar(x+.17,[1.69,1.52],.32,color=blue,label='Fresh-entry lower bound')
ax.axhline(1.6,color=orange,ls='--',label='Requirement 1.6')
for xx,val in zip(x-.17,[4,5.7]):ax.text(xx,val+.12,str(val),ha='center',fontsize=9)
for xx,val in zip(x+.17,[1.69,1.52]):ax.text(xx,val+.18,str(val),ha='center',fontsize=9)
ax.set(xticks=x,xticklabels=['Washed','Unwashed'],ylim=(0,6.5),ylabel='Amount per original aliquot')
ax.set_title('A   Matched histories; fresh amount = 2.1',loc='left',fontsize=11)
ax.legend(loc='upper center',bbox_to_anchor=(.5,-.12),fontsize=8,frameon=False)
ax=axs[1]; js=np.linspace(1.6,3.5,250)
ls=[lower(5.8,3.8,10,.05,.9,j,.2) for j in js]
ax.plot(js,ls,color=blue,lw=2)
ax.axhline(1.6,color=orange,ls='--')
ax.axvline(179/85,color=gray,ls=':')
ax.scatter([2],[1.69],color=blue)
ax.text(2.14,1.67,'J ≤ 2.1059',fontsize=9)
ax.set(xlabel='Pre-wash reserve upper bound J',ylabel='Certified fresh-entry lower bound',ylim=(0,2.3))
ax.set_title('B   Reserve uncertainty spends the margin',loc='left',fontsize=11)
save(fig,'material')

fig,axs=plt.subplots(1,2,figsize=(10,3.5),layout='constrained')
ax=axs[0];ax.set(xlim=(0,1),ylim=(0,1));ax.axis('off')
nodes={'X':(.2,.75),'Z':(.8,.75),'B':(.5,.2)}
for label,(xx,yy) in nodes.items():
    ax.text(xx,yy,label,fontsize=16,weight='bold',ha='center',va='center',bbox=dict(boxstyle='circle,pad=.65',fc='#EDF3F8',ec=blue))
def arrow(start,end,text,xy,rad=0):
    ax.add_patch(FancyArrowPatch(start,end,arrowstyle='->',mutation_scale=13,color=gray,lw=1.6,connectionstyle=f'arc3,rad={rad}'))
    ax.text(*xy,text,fontsize=9,ha='center',va='center')
arrow((.28,.8),(.72,.8),'Target use k',(.5,.95),-.1)
arrow((.72,.68),(.28,.68),'Regeneration p',(.5,.57),-.1)
arrow((.18,.64),(.41,.24),'Binding',(.15,.41))
arrow((.43,.31),(.27,.66),'Dissociation',(.39,.44))
arrow((.58,.25),(.82,.64),'Release c\n+ reporter product',(.79,.36))
ax.set_title('A   Bound cofactor remains in the inventory',loc='left',fontsize=11)
ax=axs[1];cs=np.logspace(-1,1.3,300)
ax.semilogx(cs,.5*(1+1/cs),color=blue,lw=2,label='Explicit bound complex')
ax.axhline(.5,color=gray,ls='--',label='Instantaneous turnover')
ax.scatter([.2],[3],color=orange,zorder=3)
ax.annotate('c = 0.2: sixfold cost',xy=(.2,3),xytext=(.36,3.65),arrowprops=dict(arrowstyle='-',color=gray),fontsize=9)
ax.set(xlabel='Catalytic release coefficient c (p = k = 1)',ylabel='Output loss / reporter product',ylim=(0,5.8))
ax.set_title('B   Activity alone misses storage cost',loc='left',fontsize=11)
ax.legend(frameon=False,fontsize=8,loc='upper right')
save(fig,'reporter')
print(json.dumps(results,indent=2))
