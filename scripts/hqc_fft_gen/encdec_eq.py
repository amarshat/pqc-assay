"""Generate EncDec.thy: encode<p> = encodeIdx<p> and decode<p> = decodeIdx<p> at hqc-1/3/5.
The hqc-1 proofs (ed_*.txt beside this script) are the template; the per-size parts are
instantiated by token replacement. Usage: python3 scripts/hqc_fft_gen/encdec_eq.py OUT.thy, or with
--check to compare against the committed spec/isabelle/hqc-fft/n35/EncDec.thy."""
import re, sys
import os
S = os.path.dirname(os.path.abspath(__file__)) + '/'
generic = open(S + 'ed_generic.txt').read()
enc = open(S + 'ed_enc.txt').read()
dec = open(S + 'ed_dec.txt').read()

# Tokenize the hqc-1 text. Order matters (longer strings first).
ENC_TOK = [
    ("drop'`{9,3,bool}", "drop'`{@CD@,3,bool}"),
    ("(12, bool) seq", "(@QB@, bool) seq"), (":: 12 word", ":: @QB@ word"),
    ("x < 4096", "x < @QP@"),
    ("0x200 * j", "@EH@ * j"), ("(14, bool) seq", "(@EB@, bool) seq"),
    ("512 * j + e < 16384", "@NE@ * j + e < @BITS@"),
    ("(seq_to_word (FFTEnc.flat fx)) (512 * j + e)", "(seq_to_word (FFTEnc.flat fx)) (@NE@ * j + e)"),
    ("(512 * j + e) div 64 = 8 * j + e div 64", "(@NE@ * j + e) div 64 = @W8@ * j + e div 64"),
    ("(512 * j + e) mod 64", "(@NE@ * j + e) mod 64"),
    ("8 * j + e div 64", "@W8@ * j + e div 64"),
    ("512 * j + e = e + 64 * (8 * j)", "@NE@ * j + e = e + 64 * (@W8@ * j)"), ("i + 8 * (8 * j)", "i + 8 * (@W8@ * j)"),
    ("8 * j + i div 8", "@W8@ * j + i div 8"),
    ("64 * j + i", "@CI@ * j + i"),
    ("0x40", "@CH@"),
    ("e div 8 < 64", "e div 8 < @CI@"),
    ("i < 64", "i < @CI@"),
    ("e < 512", "e < @NE@"),
    ("[0..<64]", "[0..<@CI@]"),
    ("(256, w64) seq", "(@NW@, w64) seq"), ("p < 16384", "p < @BITS@"), ("length xs = 256", "length xs = @NW@"),
    ("collect64", "collect@CI@"),
    ("FFTEnc.flat fx", "FFTEnc.flat@P@ fx"), ("flat_list", "flat@P@_list"),
    ("rule encode_bit)", "rule encode_bit@P@)"),
    ("FFTEnc.encodeIdx", "FFTEnc.encodeIdx@P@"),
    ("FFTEnc.encode_def", "FFTEnc.encode@P@_def"),
    ("FFTEnc.encode fx", "FFTEnc.encode@P@ fx"),
]
DEC_TOK = [
    ("(12, bool) seq", "(@QBD@, bool) seq"),
    ("(512, w64) seq", "(@NWD@, w64) seq"),
    ("drop'`{6,6,bool}", "drop'`{6,@ID@,bool}"), ("take'`{6,6,bool}", "take'`{6,@ID@,bool}"),
    ("group_list 64 8", "group_list @NB@ 8"),
    ("group_list 512 64", "group_list @NWD@ 64"),
    ("[0..<4096]", "[0..<@NBY@]"), ("length xs = 4096", "length xs = @NBY@"), ("4096 * 8", "@NBY@ * 8"),
    ("512 * 64", "@NWD@ * 64"), ("511 - i", "@NWD1@ - i"), ("i < 512", "i < @NWD@"),
    ("p < 32768", "p < @PB@"), ("q < 4096", "q < @NBY@"),
    ("q mod 64", "q mod @NB@"), ("q div 64", "q div @NB@"), ("i < 64", "i < @NB@"),
    ("p div 8 mod 64", "p div 8 mod @NB@"), ("p mod 512", "p mod @NB8@"), ("p div 8 div 64", "p div 8 div @NB@"),
    ("p div 512", "p div @NB8@"), ("[of p 8 64]", "[of p 8 @NB@]"),
    ("FFTEnc.unflat2_def", "FFTEnc.unflat2@P@_def"),
    ("decodeIdx_bit", "decodeIdx@P@_bit"),
    ("FFTEnc.decodeIdx", "FFTEnc.decodeIdx@P@"),
    ("FFTEnc.decode_def", "FFTEnc.decode@P@_def"),
    ("FFTEnc.decode fx", "FFTEnc.decode@P@ fx"),
]
NAMES_ENC = ['encode_list', 'encode_nth', 'w12', 'u12', 'cidx2', 'cidx', 'collect64_nth', 'flat_bit',
             'encodeIdx_word', 'encode_word', 'encode_is_encodeIdx']
NAMES_DEC = ['qw', 'OB_bit', 'OB', 'decode_list', 'decode_bit', 'q6m', 'q6d', 'rows_nth', 'decode_is_decodeIdx']

def tok(text, toks):
    for a, b in toks:
        assert a in text, a
        text = text.replace(a, b)
    return text

def rename(text, names, sfx):
    for n in names:
        text = re.sub(r'(?<![A-Za-z0-9_.])' + n + r'(?![A-Za-z0-9_\'])', n + '_' + sfx, text)
    return text

P = {
 '1': dict(P='', QB=12, QP=4096, EH='0x200', EB=14, NE=512, BITS=16384, W8=8, CI=64, CH='0x40', CD=9, NW=256,
           QBD=12, NWD=512, ID=6, NB=64, NBY=4096, NWD1=511, PB=32768, NB8=512),
 '3': dict(P='3', QB=13, QP=8192, EH='0x400', EB=16, NE=1024, BITS=32768, W8=16, CI=128, CH='0x80', CD=10, NW=512,
           QBD=13, NWD=1024, ID=7, NB=128, NBY=8192, NWD1=1023, PB=65536, NB8=1024),
 '5': dict(P='5', QB=14, QP=16384, EH='0x800', EB=17, NE=2048, BITS=65536, W8=32, CI=256, CH='0x100', CD=11, NW=1024,
           QBD=14, NWD=2048, ID=8, NB=256, NBY=16384, NWD1=2047, PB=131072, NB8=2048),
}
# hqc-1 flat/unflat names have no suffix, but hqc-1's unflat is unflat2, hqc-3's unflat23.
def inst(tmpl, p):
    d = dict(P[p])
    out = tmpl
    for k in sorted(d, key=len, reverse=True):
        out = out.replace('@' + k + '@', str(d[k]))
    assert '@' not in out, re.findall(r'@\w+@', out)
    return out

encT = tok(enc, ENC_TOK)
decT = tok(dec, DEC_TOK)
# round trip check at hqc-1
assert inst(encT, '1') == enc, 'enc roundtrip'
assert inst(decT, '1') == dec, 'dec roundtrip'

parts = []
for p in ['1', '3', '5']:
    e = inst(encT, p); d = inst(decT, p)
    sfx = p
    e = rename(e, NAMES_ENC, sfx); d = rename(d, NAMES_DEC, sfx)
    d = d.replace('OB_def', 'OB_%s_def' % sfx).replace('qw_def', 'qw_%s_def' % sfx)
    parts.append('subsection \\<open>hqc-%s\\<close>\n\n' % p + e + d)

body = '\n'.join(parts)
# Final theorem names.
for p, sfx in [('1', ''), ('3', '3'), ('5', '5')]:
    body = body.replace('theorem encode_is_encodeIdx_%s:' % p, 'theorem encode%s_eq_encodeIdx%s:' % (sfx, sfx))
    body = body.replace('theorem decode_is_decodeIdx_%s:' % p, 'theorem decode%s_eq_decodeIdx%s:' % (sfx, sfx))
hdr = open(S + 'ed_header.txt').read()
out = hdr + generic + '\n' + body + 'end\nend\n'
if sys.argv[1] == '--check':
    ref = os.path.join(S, '../../spec/isabelle/hqc-fft/n35/EncDec.thy')
    if open(ref).read() != out:
        sys.exit('EncDec.thy differs from the generator output')
    print('OK: EncDec.thy matches the generator')
else:
    open(sys.argv[1], 'w').write(out)
