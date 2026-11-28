"""Independent reference vectors; requires pycryptodome (Crypto.Hash.keccak).
These check formulas, not an EVM run or universal storage-layout agreement.
"""
from Crypto.Hash import keccak

W = 2**256

def digest(data):
    return int.from_bytes(keccak.new(digest_bits=256, data=data).digest(), "big")

def word(n):
    return (n % W).to_bytes(32, "big")

vectors = {
    "words[3]": ((digest(word(7)) + 3) % W,
        0xa66cc928b5edb82af9bd49922954155ab7b0942694bea4ce44661d9a8736c68b),
    "wallets[5].stash[9]": (digest(word(9) + word(digest(word(5) + word(9)) + 1)),
        0x24ca46cb27a3a19b4f1680b91a5b967a5f2bbf9ba773a8b64741dc16a52f7a90),
    "bits[1] slot (byte offset 1)": (digest(word(8)),
        0xf3f7a9fe364faab93b216da50a3214154f22a0a2b415b23a84c8169e8b636ee3),
    "ERC-7201 example.storage.Layout": (
        digest(word(digest(b"example.storage.Layout") - 1)) & (W - 256),
        0x1e0ff7cc49d2ef7d2fd80942c4710ca44af1d633174b1be50f21e91312d81200),
}
for label, (actual, expected) in vectors.items():
    assert actual == expected, (label, hex(actual), hex(expected))
    print("PASS", label, hex(actual))
