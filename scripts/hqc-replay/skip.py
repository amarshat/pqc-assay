#!/usr/bin/env python3
"""Write one copy of a v5.1.0 hqc-kem.c (shipped or hardened) per call skip of paper 2's fault model:
the call runs, but its outputs go to scratch buffers, so the real destinations keep their
zero-initialized values. Only calls inside hqc_kem_decaps_internal are changed. Usage:
  skip.py <hqc-kem.c> <outdir> <tag>   -> <outdir>/kem_<tag>_s<k>.c for k in SKIPS
"""
import sys

SCRATCH = """    shake256_xof_ctx f_ctx = {0};
    uint8_t f_seed[SEED_BYTES] = {0};
    uint8_t f_sigma[PARAM_K] = {0};
    uint8_t f_ek[PUBLIC_KEY_BYTES_PKE] = {0};
    uint8_t f_dk[SECRET_KEY_BYTES_PKE] = {0};
    uint64_t f_u[VEC_N_PKE_WORDS] = {0};
    uint64_t f_v[VEC_N1N2_PKE_WORDS] = {0};
    uint8_t f_salt[SALT_BYTES] = {0};
    uint64_t f_m[(PARAM_K + 7) / 8] = {0};
    uint8_t f_hek[SEED_BYTES] = {0};
"""
SKIPS = [
    ("xof_init", "xof_init_dom_sep(&ctx_kem, dk_kem,", "xof_init_dom_sep(&f_ctx, dk_kem,"),
    ("seed", "xof_get_bytes(&ctx_kem, seed_pke, SEED_BYTES);", "xof_get_bytes(&ctx_kem, f_seed, SEED_BYTES);"),
    ("sigma", "xof_get_bytes(&ctx_kem, sigma, PARAM_K);", "xof_get_bytes(&ctx_kem, f_sigma, PARAM_K);"),
    ("keygen", "hqc_pke_keygen(ek_pke, dk_pke, seed_pke);", "hqc_pke_keygen(f_ek, f_dk, seed_pke);"),
    ("parse", "hqc_c_kem_from_string(c_pke_u, c_pke_v, salt, c_kem);", "hqc_c_kem_from_string(f_u, f_v, f_salt, c_kem);"),
    ("decrypt", "hqc_pke_decrypt((uint64_t *)m_prime,", "hqc_pke_decrypt(f_m,"),
    ("hash_h", "hash_h(hash_ek_pke, ek_pke);", "hash_h(f_hek, ek_pke);"),
]

src, out, tag = sys.argv[1:4]
text = open(src).read()
start = text.index("static int8_t hqc_kem_decaps_internal(")
end = text.index("\n}\n", start)
head, body, tail = text[:start], text[start:end], text[end:]
anchor = "    uint8_t result;\n"
assert body.count(anchor) == 1
for k, (name, old, new) in enumerate(SKIPS):
    assert body.count(old) == 1, (name, body.count(old))
    b = body.replace(anchor, anchor + SCRATCH).replace(old, new)
    open(f"{out}/kem_{tag}_s{k}.c", "w").write(head + b + tail)
    print(f"s{k} {name}")
