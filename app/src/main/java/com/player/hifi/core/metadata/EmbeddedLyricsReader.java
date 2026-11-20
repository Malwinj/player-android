package com.player.hifi.core.metadata;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.channels.FileChannel;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.regex.Pattern;

/**
 * Reads lyrics embedded in audio file tags without any third-party library.
 *
 * Supported: MP3 (ID3v2.2/2.3/2.4: USLT, SYLT and TXXX:LYRICS), FLAC (Vorbis comment),
 * M4A/MP4 (the (c)lyr atom) and Ogg Vorbis / Opus (Vorbis comment).
 *
 * Only the tag areas are read (random access), so large cover art is skipped
 * instead of being loaded. Returns plain text, or LRC text when the tag holds
 * timestamps, so it can be passed straight to LyricsParser.parseRawLyrics().
 */
public final class EmbeddedLyricsReader {

    private static final int MAX_FRAME_BYTES = 4 * 1024 * 1024;
    private static final int MAX_COMMENT_BYTES = 16 * 1024 * 1024;
    private static final int MAX_MP4_DEPTH = 6;

    private static final Pattern LRC_STAMP =
            Pattern.compile("\\[\\d{1,3}:\\d{2}(?:[.:]\\d{1,3})?]");

    private EmbeddedLyricsReader() {}

    /** Returns lyrics text found in the file's tags, or null if none / unsupported. */
    public static String read(FileChannel ch) {
        try {
            byte[] head = readAt(ch, 0, 12);
            if (head.length < 8) return null;

            if (head[0] == 'I' && head[1] == 'D' && head[2] == '3') {
                long end = id3TagEnd(ch);
                String fromId3 = readId3(ch);
                if (fromId3 != null) return fromId3;
                // Some FLAC files carry a leading ID3 tag.
                byte[] after = readAt(ch, end, 4);
                if (after.length == 4 && after[0] == 'f' && after[1] == 'L' && after[2] == 'a' && after[3] == 'C') {
                    return readFlac(ch, end);
                }
                return null;
            }
            if (head[0] == 'f' && head[1] == 'L' && head[2] == 'a' && head[3] == 'C') {
                return readFlac(ch, 0);
            }
            if (head[0] == 'O' && head[1] == 'g' && head[2] == 'g' && head[3] == 'S') {
                return readOgg(ch);
            }
            if (head.length >= 8 && head[4] == 'f' && head[5] == 't' && head[6] == 'y' && head[7] == 'p') {
                return walkMp4(ch, 0, ch.size(), 0);
            }
            return null;
        } catch (IOException | RuntimeException e) {
            return null;
        }
    }

    // ------------------------------------------------------------------ ID3v2

    private static long id3TagEnd(FileChannel ch) throws IOException {
        byte[] h = readAt(ch, 0, 10);
        if (h.length < 10) return 0;
        long end = 10 + synchsafe(h, 6);
        if ((h[3] & 0xFF) == 4 && (h[5] & 0x10) != 0) end += 10; // footer
        return end;
    }

    private static String readId3(FileChannel ch) throws IOException {
        byte[] h = readAt(ch, 0, 10);
        if (h.length < 10) return null;
        int major = h[3] & 0xFF;
        if (major < 2 || major > 4) return null;
        int flags = h[5] & 0xFF;
        long end = 10 + synchsafe(h, 6);
        boolean tagUnsync = (flags & 0x80) != 0;

        long pos = 10;
        if ((flags & 0x40) != 0 && major >= 3) { // extended header
            byte[] e = readAt(ch, pos, 4);
            if (e.length < 4) return null;
            pos += (major == 4) ? synchsafe(e, 0) : 4 + be32(e, 0);
        }

        int idLen = major == 2 ? 3 : 4;
        int hdrLen = major == 2 ? 6 : 10;
        List<String> candidates = new ArrayList<>();

        while (pos + hdrLen <= end) {
            byte[] fh = readAt(ch, pos, hdrLen);
            if (fh.length < hdrLen || fh[0] == 0) break; // padding
            String id = new String(fh, 0, idLen, StandardCharsets.ISO_8859_1);
            long fsize;
            int fflags = 0;
            if (major == 2) {
                fsize = ((fh[3] & 0xFF) << 16) | ((fh[4] & 0xFF) << 8) | (fh[5] & 0xFF);
            } else if (major == 3) {
                fsize = be32(fh, 4);
                fflags = ((fh[8] & 0xFF) << 8) | (fh[9] & 0xFF);
            } else {
                fsize = synchsafe(fh, 4);
                fflags = ((fh[8] & 0xFF) << 8) | (fh[9] & 0xFF);
            }
            long dataPos = pos + hdrLen;
            if (fsize < 0 || dataPos + fsize > end) break;

            boolean uslt = id.equals("USLT") || id.equals("ULT");
            boolean sylt = id.equals("SYLT") || id.equals("SLT");
            boolean txxx = id.equals("TXXX") || id.equals("TXX");
            if ((uslt || sylt || txxx) && fsize > 0 && fsize <= MAX_FRAME_BYTES) {
                boolean compressedOrEncrypted = (major == 3 && (fflags & 0x00C0) != 0)
                        || (major == 4 && (fflags & 0x000C) != 0);
                if (!compressedOrEncrypted) {
                    byte[] data = readAt(ch, dataPos, (int) fsize);
                    if (major == 4 && (fflags & 0x0001) != 0 && data.length > 4) {
                        data = Arrays.copyOfRange(data, 4, data.length); // data length indicator
                    }
                    boolean frameUnsync = (major == 4) ? (fflags & 0x0002) != 0 : tagUnsync;
                    if (frameUnsync) data = deunsync(data);
                    String text = uslt ? decodeUslt(data) : (sylt ? decodeSylt(data) : decodeTxxxLyrics(data));
                    if (text != null && !text.trim().isEmpty()) candidates.add(text);
                }
            }
            pos = dataPos + fsize;
        }
        return pickBest(candidates);
    }

    private static String decodeUslt(byte[] d) {
        if (d.length < 5) return null;
        int enc = d[0] & 0xFF;
        int p = skipTerminated(d, 4, enc); // skip encoding byte + 3-byte language, then descriptor
        if (p < 0 || p > d.length) return null;
        return decodeText(d, p, d.length, enc);
    }

    /** Custom text frame whose description is a lyrics key (e.g. TXXX:LYRICS). */
    private static String decodeTxxxLyrics(byte[] d) {
        if (d.length < 3) return null;
        int enc = d[0] & 0xFF;
        int q = findTerminator(d, 1, enc);
        if (q < 0) return null;
        String desc = decodeText(d, 1, q, enc).trim().toUpperCase(Locale.ROOT);
        // "USLT" as a description is what ffmpeg writes for -metadata lyrics=...
        if (!(desc.equals("LYRICS") || desc.equals("UNSYNCEDLYRICS") || desc.equals("USLT")
                || desc.equals("SYNCEDLYRICS") || desc.equals("UNSYNCED LYRICS"))) {
            return null;
        }
        return decodeText(d, q + termLen(enc), d.length, enc);
    }

    /** SYLT with millisecond timestamps is converted to LRC text. */
    private static String decodeSylt(byte[] d) {
        if (d.length < 7) return null;
        int enc = d[0] & 0xFF;
        int tsFormat = d[4] & 0xFF;
        if (tsFormat != 2) return null; // 1 = MPEG frames, cannot convert without the audio
        int p = skipTerminated(d, 6, enc); // skip content type, then descriptor
        if (p < 0) return null;
        StringBuilder sb = new StringBuilder();
        while (p < d.length) {
            int q = findTerminator(d, p, enc);
            if (q < 0 || q + termLen(enc) + 4 > d.length) break;
            String line = decodeText(d, p, q, enc);
            int t = q + termLen(enc);
            long ms = be32(d, t);
            p = t + 4;
            if (line == null) continue;
            line = line.replace("\r", "").replace("\n", " ").trim();
            if (line.isEmpty()) continue;
            long mins = ms / 60000;
            long secs = (ms / 1000) % 60;
            long cs = (ms % 1000) / 10;
            sb.append(String.format(Locale.US, "[%02d:%02d.%02d]%s%n", mins, secs, cs, line));
        }
        return sb.length() == 0 ? null : sb.toString();
    }

    private static int termLen(int enc) {
        return (enc == 1 || enc == 2) ? 2 : 1;
    }

    private static int findTerminator(byte[] d, int from, int enc) {
        if (termLen(enc) == 2) {
            for (int i = from; i + 1 < d.length; i += 2) {
                if (d[i] == 0 && d[i + 1] == 0) return i;
            }
            return -1;
        }
        for (int i = from; i < d.length; i++) {
            if (d[i] == 0) return i;
        }
        return -1;
    }

    private static int skipTerminated(byte[] d, int from, int enc) {
        int q = findTerminator(d, from, enc);
        return q < 0 ? -1 : q + termLen(enc);
    }

    private static String decodeText(byte[] d, int from, int to, int enc) {
        if (from >= to) return "";
        byte[] b = Arrays.copyOfRange(d, from, to);
        String s;
        switch (enc) {
            case 1: {
                if (b.length >= 2 && (b[0] & 0xFF) == 0xFE && (b[1] & 0xFF) == 0xFF) {
                    s = new String(b, 2, b.length - 2, StandardCharsets.UTF_16BE);
                } else if (b.length >= 2 && (b[0] & 0xFF) == 0xFF && (b[1] & 0xFF) == 0xFE) {
                    s = new String(b, 2, b.length - 2, StandardCharsets.UTF_16LE);
                } else {
                    s = new String(b, StandardCharsets.UTF_16LE);
                }
                break;
            }
            case 2:
                s = new String(b, StandardCharsets.UTF_16BE);
                break;
            case 3:
                s = new String(b, StandardCharsets.UTF_8);
                break;
            default: {
                // Many taggers declare ISO-8859-1 but store UTF-8 (e.g. Cyrillic lyrics).
                String utf8 = strictUtf8(b);
                s = utf8 != null ? utf8 : new String(b, StandardCharsets.ISO_8859_1);
            }
        }
        return trimNulls(s).replace("\r\n", "\n").replace('\r', '\n');
    }

    private static String strictUtf8(byte[] b) {
        boolean hasHigh = false;
        for (byte x : b) {
            if ((x & 0x80) != 0) { hasHigh = true; break; }
        }
        if (!hasHigh) return new String(b, StandardCharsets.ISO_8859_1);
        try {
            return StandardCharsets.UTF_8.newDecoder()
                    .onMalformedInput(CodingErrorAction.REPORT)
                    .onUnmappableCharacter(CodingErrorAction.REPORT)
                    .decode(ByteBuffer.wrap(b)).toString();
        } catch (CharacterCodingException e) {
            return null;
        }
    }

    private static byte[] deunsync(byte[] in) {
        ByteArrayOutputStream out = new ByteArrayOutputStream(in.length);
        for (int i = 0; i < in.length; i++) {
            out.write(in[i]);
            if ((in[i] & 0xFF) == 0xFF && i + 1 < in.length && in[i + 1] == 0) i++;
        }
        return out.toByteArray();
    }

    // ------------------------------------------------------------------ FLAC

    private static String readFlac(FileChannel ch, long start) throws IOException {
        long size = ch.size();
        long pos = start + 4;
        while (pos + 4 <= size) {
            byte[] h = readAt(ch, pos, 4);
            if (h.length < 4) return null;
            boolean last = (h[0] & 0x80) != 0;
            int type = h[0] & 0x7F;
            int len = ((h[1] & 0xFF) << 16) | ((h[2] & 0xFF) << 8) | (h[3] & 0xFF);
            pos += 4;
            if (type == 4) { // VORBIS_COMMENT; PICTURE and other blocks are skipped
                if (len > MAX_COMMENT_BYTES) return null;
                return pickBest(parseVorbisComments(readAt(ch, pos, len), 0));
            }
            pos += len;
            if (last) break;
        }
        return null;
    }

    // ------------------------------------------------------------------ Ogg Vorbis / Opus

    private static String readOgg(FileChannel ch) throws IOException {
        long size = ch.size();
        long pos = 0;
        int packetIndex = 0;
        ByteArrayOutputStream comment = new ByteArrayOutputStream();
        while (pos + 27 <= size) {
            byte[] ph = readAt(ch, pos, 27);
            if (ph.length < 27 || ph[0] != 'O' || ph[1] != 'g' || ph[2] != 'g' || ph[3] != 'S') return null;
            int segs = ph[26] & 0xFF;
            byte[] table = readAt(ch, pos + 27, segs);
            if (table.length < segs) return null;
            int total = 0;
            for (byte s : table) total += (s & 0xFF);
            long bodyPos = pos + 27 + segs;
            byte[] body = readAt(ch, bodyPos, total);
            int off = 0;
            for (int i = 0; i < segs; i++) {
                int l = table[i] & 0xFF;
                if (off + l > body.length) return null;
                if (packetIndex == 1) comment.write(body, off, l);
                off += l;
                if (l < 255) { // packet boundary
                    if (packetIndex == 1) {
                        byte[] pkt = comment.toByteArray();
                        int start;
                        if (pkt.length > 8 && new String(pkt, 0, 8, StandardCharsets.ISO_8859_1).equals("OpusTags")) {
                            start = 8;
                        } else if (pkt.length > 7 && pkt[0] == 3
                                && new String(pkt, 1, 6, StandardCharsets.ISO_8859_1).equals("vorbis")) {
                            start = 7;
                        } else {
                            return null;
                        }
                        return pickBest(parseVorbisComments(pkt, start));
                    }
                    packetIndex++;
                }
            }
            if (comment.size() > MAX_COMMENT_BYTES) return null;
            pos = bodyPos + total;
        }
        return null;
    }

    // ------------------------------------------------------------------ Vorbis comments

    private static List<String> parseVorbisComments(byte[] b, int off) {
        List<String> out = new ArrayList<>();
        try {
            ByteBuffer bb = ByteBuffer.wrap(b).order(ByteOrder.LITTLE_ENDIAN);
            bb.position(off);
            int vendorLen = bb.getInt();
            if (vendorLen < 0 || vendorLen > bb.remaining()) return out;
            bb.position(bb.position() + vendorLen);
            long count = bb.getInt() & 0xFFFFFFFFL;
            for (long i = 0; i < count && bb.remaining() >= 4; i++) {
                int len = bb.getInt();
                if (len < 0 || len > bb.remaining()) break;
                byte[] e = new byte[len];
                bb.get(e);
                // Cover art (METADATA_BLOCK_PICTURE) can be huge: skip it quickly.
                if (len > 8 && (e[0] == 'M' || e[0] == 'm')) {
                    String head = new String(e, 0, Math.min(len, 22), StandardCharsets.ISO_8859_1)
                            .toUpperCase(Locale.ROOT);
                    if (head.startsWith("METADATA_BLOCK_PICTURE=")) continue;
                }
                String s = new String(e, StandardCharsets.UTF_8);
                int eq = s.indexOf('=');
                if (eq <= 0) continue;
                String key = s.substring(0, eq).toUpperCase(Locale.ROOT);
                if (key.equals("LYRICS") || key.equals("UNSYNCEDLYRICS")
                        || key.equals("SYNCEDLYRICS") || key.equals("UNSYNCED LYRICS")) {
                    String v = trimNulls(s.substring(eq + 1)).replace("\r\n", "\n").replace('\r', '\n');
                    if (!v.trim().isEmpty()) out.add(v);
                }
            }
        } catch (RuntimeException ignored) {
            // truncated block: return what we have
        }
        return out;
    }

    // ------------------------------------------------------------------ MP4

    private static String walkMp4(FileChannel ch, long start, long end, int depth) throws IOException {
        if (depth > MAX_MP4_DEPTH) return null;
        long pos = start;
        while (pos + 8 <= end) {
            byte[] h = readAt(ch, pos, 16);
            if (h.length < 8) return null;
            long size = be32(h, 0);
            long hdr = 8;
            if (size == 1) {
                if (h.length < 16) return null;
                size = be64(h, 8);
                hdr = 16;
            } else if (size == 0) {
                size = end - pos;
            }
            if (size < hdr) return null;
            if (pos + size > end) size = end - pos;
            long bodyStart = pos + hdr;
            long bodyEnd = pos + size;
            int b4 = h[4] & 0xFF, b5 = h[5] & 0xFF, b6 = h[6] & 0xFF, b7 = h[7] & 0xFF;
            String type = new String(h, 4, 4, StandardCharsets.ISO_8859_1);

            if (type.equals("moov") || type.equals("udta") || type.equals("ilst")) {
                String r = walkMp4(ch, bodyStart, bodyEnd, depth + 1);
                if (r != null) return r;
            } else if (type.equals("meta")) {
                byte[] m = readAt(ch, bodyStart, 8);
                boolean fullBox = !(m.length == 8 && m[4] == 'h' && m[5] == 'd' && m[6] == 'l' && m[7] == 'r');
                String r = walkMp4(ch, bodyStart + (fullBox ? 4 : 0), bodyEnd, depth + 1);
                if (r != null) return r;
            } else if (b4 == 0xA9 && b5 == 'l' && b6 == 'y' && b7 == 'r') {
                long bodyLen = bodyEnd - bodyStart;
                if (bodyLen > 16 && bodyLen <= MAX_FRAME_BYTES) {
                    byte[] item = readAt(ch, bodyStart, (int) bodyLen);
                    if (item.length > 16 && item[4] == 'd' && item[5] == 'a' && item[6] == 't' && item[7] == 'a') {
                        String text = trimNulls(new String(item, 16, item.length - 16, StandardCharsets.UTF_8))
                                .replace("\r\n", "\n").replace('\r', '\n');
                        if (!text.trim().isEmpty()) return text;
                    }
                }
            }
            if (bodyEnd <= pos) return null;
            pos = bodyEnd;
        }
        return null;
    }

    // ------------------------------------------------------------------ helpers

    /** Prefers timestamped (LRC) text, otherwise the first non-empty candidate. */
    private static String pickBest(List<String> candidates) {
        String firstPlain = null;
        for (String c : candidates) {
            if (LRC_STAMP.matcher(c).find()) return c;
            if (firstPlain == null) firstPlain = c;
        }
        return firstPlain;
    }

    private static String trimNulls(String s) {
        int end = s.length();
        while (end > 0 && s.charAt(end - 1) == '\u0000') end--;
        int start = 0;
        while (start < end && s.charAt(start) == '\u0000') start++;
        return s.substring(start, end);
    }

    private static long synchsafe(byte[] b, int o) {
        return ((long) (b[o] & 0x7F) << 21) | ((b[o + 1] & 0x7F) << 14)
                | ((b[o + 2] & 0x7F) << 7) | (b[o + 3] & 0x7F);
    }

    private static long be32(byte[] b, int o) {
        return ((long) (b[o] & 0xFF) << 24) | ((b[o + 1] & 0xFF) << 16)
                | ((b[o + 2] & 0xFF) << 8) | (b[o + 3] & 0xFF);
    }

    private static long be64(byte[] b, int o) {
        return (be32(b, o) << 32) | be32(b, o + 4);
    }

    private static byte[] readAt(FileChannel ch, long pos, int len) throws IOException {
        if (len < 0) throw new IOException("negative length");
        ByteBuffer bb = ByteBuffer.allocate(len);
        while (bb.hasRemaining()) {
            int n = ch.read(bb, pos + bb.position());
            if (n < 0) break;
        }
        byte[] out = bb.array();
        return bb.position() == len ? out : Arrays.copyOf(out, bb.position());
    }
            }
