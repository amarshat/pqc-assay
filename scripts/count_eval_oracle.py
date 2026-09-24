import re, sys, pathlib
tot=0; rows=[]
for p in sorted(pathlib.Path('spec/isabelle').rglob('*.thy')) + sorted(pathlib.Path('afp').rglob('*.thy')):
    s=p.read_text()
    s=re.sub(r'\(\*.*?\*\)', '', s, flags=re.S)          # strip (* ... *)
    s=re.sub(r'text\s*\\<open>.*?\\<close>', '', s, flags=re.S)  # strip text blocks
    n=len(re.findall(r'\bby\s+eval\b', s)) + len(re.findall(r'\bby\s*\(\s*eval\s*\)', s))
    if n: rows.append((str(p), n)); tot+=n
for f,n in sorted(rows, key=lambda r:-r[1]): print(f"{n:>4}  {f}")
print(f"\nTOTAL by-eval (comments and text blocks excluded): {tot}")
gated = sum(n for f,n in rows if any(k in f for k in ('tier2/work','tier2/invwork','kem/work','tier2/Bridge_Word','Assay_Equivalence','tier2/signwork','tier2/invsignwork')))
print(f"of which in sessions built by `make verify`: {gated}")
