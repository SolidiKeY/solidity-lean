#!/usr/bin/env python3
"""Opt-in bounded gzip inspection for H871; no inventory promotion yet.

Frozen classifiers and their observation interfaces remain unchanged. This
module only checks bytes supplied by a future exact-object reviewed adapter.
Decoded content is historical text, never execution or deletion evidence.
"""
import hashlib
import zlib

# Separate bounds cover compressed input and expansion. Neither is a gate or
# execution budget; no extraction, filesystem access or subprocess is performed.
MAX_COMPRESSED = 1_000_000
MAX_DECODED = 1_000_000


def decode_member(raw):
    """Accept exactly one complete gzip member containing bounded UTF-8 text."""
    if not isinstance(raw, bytes) or len(raw) > MAX_COMPRESSED:
        raise ValueError('compressed input type or size')
    decoder = zlib.decompressobj(16 + zlib.MAX_WBITS)
    try:
        decoded = decoder.decompress(raw, MAX_DECODED + 1)
    except zlib.error as error:
        raise ValueError('invalid gzip member') from error
    if (len(decoded) > MAX_DECODED or not decoder.eof
            or decoder.unused_data or decoder.unconsumed_tail):
        raise ValueError('oversized, incomplete or multiple gzip members')
    try:
        text = decoded.decode('utf-8', errors='strict')
    except UnicodeDecodeError as error:
        raise ValueError('gzip text is not UTF-8') from error
    if '\0' in text:
        raise ValueError('gzip text contains NUL')
    return decoded, text


def anchored_text(raw, digest, anchor):
    """Check a decompressed SHA256 and a nonempty exact complete line.

    This does not establish the compressed Git object, current consumers,
    classification, recovery, or an independent object's review.
    """
    if (not isinstance(digest, str) or len(digest) != 64
            or any(c not in '0123456789abcdef' for c in digest)
            or not isinstance(anchor, str) or not anchor.strip()
            or any(c in anchor for c in '\r\n\0')):
        raise ValueError('invalid decoded digest or full-line anchor')
    decoded, text = decode_member(raw)
    if hashlib.sha256(decoded).hexdigest() != digest or anchor not in text.splitlines():
        raise ValueError('decoded digest or full-line anchor mismatch')
    return text


def controls():
    """Pure in-process controls; no tracked files or execution observations."""
    import gzip
    content = b'historical result: unverified\nsecond line\n'
    raw = gzip.compress(content, mtime=0)
    digest = hashlib.sha256(content).hexdigest()
    assert anchored_text(raw, digest, 'historical result: unverified') == content.decode()
    assert decode_member(gzip.compress(b'', mtime=0)) == (b'', '')
    invalid = [b'', b'not gzip', raw[:-1], raw + b'x', raw + raw,
               gzip.compress(b'\xff', mtime=0), gzip.compress(b'\0', mtime=0),
               gzip.compress(b'x' * (MAX_DECODED + 1), mtime=0),
               b'x' * (MAX_COMPRESSED + 1), bytearray(raw)]
    corrupt = bytearray(raw); corrupt[-8] ^= 1; invalid.append(bytes(corrupt))
    for value in invalid:
        try:
            decode_member(value)
        except ValueError:
            pass
        else:
            raise AssertionError('unsafe gzip accepted')
    for bad_digest, bad_anchor in [(digest, 'historical result'), ('0' * 64, 'second line'),
                                   (digest.upper(), 'second line'), (digest, ''),
                                   (digest, 'second line\n'), (True, 'second line')]:
        try:
            anchored_text(raw, bad_digest, bad_anchor)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid digest/anchor accepted')
    assert len(decode_member(gzip.compress(b'x' * MAX_DECODED, mtime=0))[0]) == MAX_DECODED
    print('PASS H871 bounded gzip controls: single member, CRC, UTF-8, caps, exact digest/full line; no classification credit')


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true', required=True)
    parser.parse_args()
    controls()
