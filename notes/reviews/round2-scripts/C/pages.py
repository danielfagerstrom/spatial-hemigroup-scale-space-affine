import sys
txt=open('out/C/manuscript.txt',encoding='utf-8',errors='replace').read()
pages=txt.split('\f')
keys=["3.3 The kernel at its centre","3.4 The dimension filtration","Theorem 3.12 (","Corollary 3.13 (","Example 3.14 (","Proposition 3.15 (","Proposition 3.16 (","Proposition 3.17 (","Example 3.14, continued","A.4 The kernel at its centre","A.5 The dimension","Lemma A.2 (","Lemma A.3 (","Proposition A.4 (","Proposition A.5 (","Proposition A.6 (","Lemma A.7 (","2.6 ","2.4 ","A.1 Sources","B Verification","4 Conclusion","Figure 1:","Definition 3.9","Proposition 3.18 (","Lemma A.1 (","2.5 ","2.3 ","2.2 ","Table"]
for i,p in enumerate(pages,1):
    for k in keys:
        if k in p: print(f"p{i}: {k}")
