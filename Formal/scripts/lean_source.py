"""Extract a declaration header while retaining let expressions in its type.

This reads source text, not a Lean elaborated interface. The original module and
source-bound compiler receipt remain the authority for parsing and semantics.
"""
import re

def theorem_header(text,written_name):
    match=re.search(r'(?m)^(?:theorem|lemma) '+re.escape(written_name)+r'\b',text)
    if not match:raise ValueError('Declaration not found: '+written_name)
    start=match.start();i=match.end();depth=[];let_binding=False
    pairs={'(':')','[':']','{':'}','⦃':'⦄','⟨':'⟩'}
    while i<len(text):
        if text.startswith('--',i):
            end=text.find('\n',i);i=len(text) if end<0 else end+1;continue
        if text.startswith('/-',i):
            comments=1;i+=2
            while comments and i<len(text):
                if text.startswith('/-',i):comments+=1;i+=2
                elif text.startswith('-/',i):comments-=1;i+=2
                else:i+=1
            if comments:raise ValueError('Unclosed comment')
            continue
        c=text[i]
        if c in {'"','«'}:
            end='"' if c=='"' else '»';i+=1
            while i<len(text):
                if text[i]=='\\' and end=='"':i+=2;continue
                if text[i]==end:i+=1;break
                i+=1
            continue
        if c in pairs:depth.append(pairs[c]);i+=1;continue
        if depth and c==depth[-1]:depth.pop();i+=1;continue
        if not depth and text.startswith(':=',i):
            if let_binding:let_binding=False;i+=2;continue
            return text[start:i].rstrip()
        token=re.match(r'\w+',text[i:])
        if token:
            if not depth and token[0]=='let':let_binding=True
            i+=len(token[0]);continue
        i+=1
    raise ValueError('No outer proof assignment: '+written_name)
