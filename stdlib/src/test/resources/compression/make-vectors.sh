#!/usr/bin/env bash
# Regenerates the compression test vectors in this directory from reference
# implementations (zlib via Python, the gzip and zip command-line tools), so
# the Blaise decoders are checked against data they did not produce.
#
# The vectors are committed; rerun this only to add or change one, then
# update the tests (compression.tests.pas, gzip.tests.pas, zip.tests.pas)
# that embed them with {$EMBEDSTR}.
set -euo pipefail
cd "$(dirname "$0")"

python3 -I - <<'EOF'
import random, struct, zlib

# A short text with plenty of repeats: the original for the deflate vectors.
text = (b"The quick brown fox jumps over the lazy dog. " * 6 +
        b"Pack my box with five dozen liquor jugs! 0123456789\n" * 4 +
        b"How vexingly quick daft zebras jump.\n")
open("lorem.txt", "wb").write(text)

def raw(data, level=9, strategy=zlib.Z_DEFAULT_STRATEGY):
    c = zlib.compressobj(level, zlib.DEFLATED, -15, 9, strategy)
    return c.compress(data) + c.flush()

open("lorem.deflate-fixed", "wb").write(raw(text, strategy=zlib.Z_FIXED))
open("lorem.deflate-dynamic", "wb").write(raw(text))
open("lorem.deflate-stored", "wb").write(raw(text, level=0))
open("lorem.zlib", "wb").write(zlib.compress(text, 9))

# ~48 KiB of seeded pseudo-random words: several dynamic blocks and match
# distances beyond 16 KiB.  Only the compressed form is committed; the tests
# check the inflated length and SHA-256 printed below.
rnd = random.Random(1951)
words = [b"alpha", b"bravo", b"charlie", b"delta", b"echo", b"foxtrot",
         b"golf", b"hotel", b"india", b"juliet", b"kilo", b"lima", b"mike"]
big = b" ".join(rnd.choice(words) + str(rnd.randrange(1000)).encode()
                for _ in range(6000))[:49152]
open("words.deflate", "wb").write(raw(big, level=6))
import hashlib
print("words: %d bytes, sha256 %s" % (len(big), hashlib.sha256(big).hexdigest()))

# A gzip member with every optional header field: FEXTRA, FNAME, FCOMMENT
# and FHCRC (the gzip tool writes only FNAME).
body = b"gzip header flags test\n"
hdr = bytearray(b"\x1f\x8b\x08")
hdr.append(0x02 | 0x04 | 0x08 | 0x10)          # FHCRC FEXTRA FNAME FCOMMENT
hdr += struct.pack("<I", 1700000000) + b"\x00\x03"
extra = b"AP" + struct.pack("<H", 4) + b"\x01\x02\x03\x04"
hdr += struct.pack("<H", len(extra)) + extra
hdr += b"flags.txt\x00" + b"a comment\x00"
hdr += struct.pack("<H", zlib.crc32(bytes(hdr)) & 0xFFFF)
member = bytes(hdr) + raw(body) + struct.pack("<II", zlib.crc32(body), len(body))
open("flags.gz", "wb").write(member)

# A Zip64 archive written by hand: sizes and offset in the central directory
# are 0xFFFFFFFF with the real values in the Zip64 extra field, and the end of
# central directory points at a Zip64 end record through its locator.
name = b"zip64/hello.txt"
data = b"Hello from a Zip64 archive.\n"
comp = raw(data)
crc = zlib.crc32(data)
loc_extra = struct.pack("<HHQQ", 1, 16, len(data), len(comp))
local = (struct.pack("<IHHHHHIIIHH", 0x04034b50, 45, 0, 8, 0, 0x21, crc,
                     0xFFFFFFFF, 0xFFFFFFFF, len(name), len(loc_extra))
         + name + loc_extra + comp)
cen_extra = struct.pack("<HHQQQ", 1, 24, len(data), len(comp), 0)
central = (struct.pack("<IHHHHHHIIIHHHHHII", 0x02014b50, 45, 45, 0, 8, 0,
                       0x21, crc, 0xFFFFFFFF, 0xFFFFFFFF, len(name),
                       len(cen_extra), 0, 0, 0, 0, 0xFFFFFFFF)
           + name + cen_extra)
cd_off = len(local)
z64_off = cd_off + len(central)
z64_end = struct.pack("<IQHHIIQQQQ", 0x06064b50, 44, 45, 45, 0, 0, 1, 1,
                      len(central), cd_off)
z64_loc = struct.pack("<IIQI", 0x07064b50, 0, z64_off, 1)
eocd = struct.pack("<IHHHHIIH", 0x06054b50, 0, 0, 0xFFFF, 0xFFFF,
                   0xFFFFFFFF, 0xFFFFFFFF, 0)
open("zip64.zip", "wb").write(local + central + z64_end + z64_loc + eocd)

# An entry flagged as encrypted (general-purpose bit 0): the reader must
# refuse it, not return ciphertext.
def stored_zip(name, data, flags=0, method=0):
    crc = zlib.crc32(data)
    local = (struct.pack("<IHHHHHIIIHH", 0x04034b50, 20, flags, method, 0,
                         0x21, crc, len(data), len(data), len(name), 0)
             + name + data)
    central = (struct.pack("<IHHHHHHIIIHHHHHII", 0x02014b50, 20, 20, flags,
                           method, 0, 0x21, crc, len(data), len(data),
                           len(name), 0, 0, 0, 0, 0, 0) + name)
    eocd = struct.pack("<IHHHHIIH", 0x06054b50, 0, 0, 1, 1, len(central),
                       len(local), 0)
    return local + central + eocd
open("encrypted.zip", "wb").write(stored_zip(b"secret.txt", b"xxxxxxxx", flags=1))
# Method 14 (LZMA) is not supported: refused with a clear error.
open("lzma.zip", "wb").write(stored_zip(b"packed.bin", b"xxxxxxxx", method=14))
# An archive whose entry name escapes the extraction folder.
open("traversal.zip", "wb").write(stored_zip(b"../evil.txt", b"gotcha\n"))
EOF

# gzip(1): one member with FNAME, and two members concatenated.
gzip -9 -c lorem.txt > lorem.txt.gz
printf 'first member\n' | gzip -c > concat.gz
printf 'second member\n' | gzip -c >> concat.gz

# zip(1): a directory, a stored file (-0 for .bin via -n) and a deflated one.
rm -rf ziptree sample.zip
mkdir -p ziptree/docs
cp lorem.txt ziptree/docs/lorem.txt
printf 'stored bytes\000\001\002\n' > ziptree/raw.bin
touch -t 202405061530.42 ziptree/docs/lorem.txt ziptree/raw.bin ziptree/docs
(cd ziptree && zip -q -X -9 -n .bin -r ../sample.zip docs raw.bin)
rm -rf ziptree
