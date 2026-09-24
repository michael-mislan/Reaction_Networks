"""Vector editorial diagram; no simulated or empirical data."""
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

OUT=Path(__file__).resolve().parent/'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','pdf.fonttype':42,'ps.fonttype':42})
fig,ax=plt.subplots(figsize=(8.8,8.2))
fig.subplots_adjust(left=.01,right=.99,top=.99,bottom=.01)
ax.set(xlim=(0,8.8),ylim=(0,8.2));ax.axis('off')
navy='#243444';blue='#27689D';gray='#738698';orange='#A95727'
def box(x,y,w,h,title,detail,face='#EDF3F8',edge=blue,fs=10.5):
    ax.add_patch(FancyBboxPatch((x-w/2,y-h/2),w,h,boxstyle='round,pad=0.035,rounding_size=.07',fc=face,ec=edge,lw=.8))
    ax.text(x,y+.13,title,ha='center',va='center',fontsize=fs+1,weight='bold',color=navy)
    ax.text(x,y-.13,detail,ha='center',va='center',fontsize=fs,color=navy)
def arrow(a,b,color=gray):
    ax.add_patch(FancyArrowPatch(a,b,arrowstyle='-|>',mutation_scale=12,color=color,lw=1.2))
steps=[
('1  Write the intended claim','What must this result let someone conclude?'),
('2  Fix the unit and conditions','Which specimen, denominator, task, and deadline?'),
('3  Trace the route to the record','Where can material, function, or observation be lost?'),
('4  Construct the competing explanation','What else fits the record but changes the decision?'),
('5  Choose and budget the repair','Observation or intervention; material, error, time, disturbance'),
('6  Validate the complete reporting rule','Test critical premises, errors, and reporting availability')]
ax.text(.65,8.02,'DESIGN AND VALIDATE',fontsize=11,color=blue,weight='bold')
ys=[7.46,6.54,5.62,4.70,3.78,2.86]
for i,((title,detail),y) in enumerate(zip(steps,ys)):
    box(4.4,y,7.45,.68,title,detail)
    if i<5:arrow((4.4,y-.37),(4.4,ys[i+1]+.37))
arrow((4.4,2.48),(4.4,2.12))
box(4.4,1.78,4.7,.6,'For each future record','Evaluable and compatible with the model?',face='#F0F1F3',edge=gray,fs=10)
arrow((2.02,1.78),(1.08,1.78));arrow((1.08,1.78),(1.08,1.20))
ax.text(1.55,1.90,'No',fontsize=10,color=orange,ha='center')
box(1.12,.78,1.94,.75,'Withhold conclusion','Unevaluable or\nincompatible: investigate',face='#FFF2E8',edge=orange,fs=8.9)
arrow((4.4,1.44),(4.4,1.17))
ax.text(4.66,1.29,'Yes',fontsize=10,color=blue)
ax.text(5.05,1.04,'Apply the prespecified decision rule',fontsize=10,ha='center',color=navy)
for x,title,detail,color in [(3.15,'Supported','Claim meets the rule',blue),(5.20,'Excluded','Claim ruled out',blue),(7.25,'Unresolved','Bounds or rule do not decide',orange)]:
    arrow((4.4,.92),(x,.73))
    box(x,.36,1.90,.54,title,detail,face='#EDF3F8' if color==blue else '#FFF2E8',edge=color,fs=7.7)
fig.savefig(OUT/'workflow.pdf',bbox_inches='tight')
fig.savefig(OUT/'workflow.png',bbox_inches='tight',dpi=160)
plt.close(fig)
