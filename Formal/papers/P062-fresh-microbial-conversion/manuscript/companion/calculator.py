"""Exact rational finite-material certificate. CLI: calculator.py [input.json]."""
from fractions import Fraction as F
from pathlib import Path
import json,sys

def facets(q1,q2,B,e,s,J,H):
    return {'nonnegative':F(0),'first_window':q1-B,'total_inventory':q1+q2-B-H,
            'measured_reserve':e*q1+q2-e*B-(s-e)*J-H,
            'scalar_retention':s*q1+q2-s*B-H}

def calculate(data):
    keys=['y1','y2','eps1','eps2','B','e','s','J','H','threshold']
    v={k:F(str(data[k])) for k in keys}
    if any(v[k]<0 for k in ['eps1','eps2','B','e','s','J','H','threshold']) or not v['e']<=v['s']<=1:
        raise ValueError('Require nonnegative bounds and 0 <= e <= s <= 1')
    upper=F(str(data['fresh_upper'])) if data.get('fresh_upper') is not None else None
    if upper is not None and upper<0: raise ValueError('fresh_upper must be nonnegative')
    base=dict(target='fresh credited inventory, two windows, micromol butyrate-equivalent per original aliquot',
      protocol=data.get('protocol','fixed two windows; pool-specific recovery'),
      evidence_kind='deterministic conditional material-model certificate',
      provenance=data.get('provenance','unspecified calibration; no empirical validation'),
      upper=str(upper) if upper is not None else None)
    if min(v['y1']+v['eps1'],v['y2']+v['eps2'])<0:
        return {**base,'outcome':'incompatible','reason':'an output interval excludes every nonnegative amount','lower':None}
    q1=max(F(0),v['y1']-v['eps1']); q2=max(F(0),v['y2']-v['eps2'])
    fs=facets(q1,q2,*(v[k] for k in ['B','e','s','J','H']))
    low=max(fs.values()); active=[k for k,x in fs.items() if x==low]
    if upper is not None and low>upper:
        outcome='incompatible'
    elif low>=v['threshold']: outcome='certified-above'
    elif upper is not None and upper<v['threshold']: outcome='certified-below'
    else: outcome='unresolved'
    # Sufficiency of feasibility here uses the conventional sharpness construction.
    # Does not imply kinetic/biological realizability outside the declared class.
    return {**base,'outcome':outcome,'lower':str(low),'active_constraints':active,
      'facets':{k:str(x) for k,x in fs.items()},
      'dominant_limitation':'pre-wash convertible reserve and activity needed for second output',
      'next_useful_measurement':'bound pre-wash reserve J, including uptake and aliquot transport; more timepoints alone are not a proved repair',
      'feasibility_scope':'exact finite material class; extra kinetics/joint observations require a separate compatibility check'}

def examples():
    b=dict(y1='6',y2='4',eps1='.2',eps2='.2',B='10',e='.05',s='.9',J='2',H='.2',threshold='1.5',
      provenance='All numerical inputs synthetic; retention and reserve require calibration')
    return {'positive':b,'unresolved':{**b,'J':'4'},'incompatible':{**b,'fresh_upper':'1'},
      'boundary':{**b,'threshold':'1.69'},'below':{**b,'y2':'1','fresh_upper':'1'},
      'negative_interval':{**b,'y2':'-1'}}

if __name__=='__main__':
    if len(sys.argv)>1: print(json.dumps(calculate(json.loads(Path(sys.argv[1]).read_text())),indent=2))
    else: print(json.dumps({k:calculate(v) for k,v in examples().items()},indent=2))
